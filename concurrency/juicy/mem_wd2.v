(* A stronger version of mem_wd2. Adapted from sepcomp/mem_wd2.v. *)
Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import VST.sepcomp.mem_lemmas.
Require Import VST.sepcomp.mem_wd.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.msl.eq_dec.

Definition mem_wd2 m := forall b ofs, memval_inject (Mem.flat_inj (Mem.nextblock m))
    (ZMap.get ofs (PMap.get b (Mem.mem_contents m))) (ZMap.get ofs (PMap.get b (Mem.mem_contents m))).

Lemma mem_wd2_alloc: forall m b lo hi m' (ALL: Mem.alloc m lo hi = (m',b))
     (WDm: mem_wd2 m), mem_wd2 m'.
Proof.
  unfold mem_wd2; intros.
  erewrite Mem.nextblock_alloc by eauto.
  destruct (eq_dec b0 b); [subst; erewrite AllocContentsUndef by eauto | erewrite AllocContentsOther by eauto].
  - rewrite ZMap.gi; constructor.
  - eapply memval_inject_incr, flat_inj_incr, Ple_succ; auto.
Qed.

Lemma mem_wd2_store: forall m b ofs v m' chunk (WDm: mem_wd2 m)
  (ST: Mem.store chunk m b ofs v = Some m')
  (V: val_valid v m), mem_wd2 m'.
Proof.
  unfold mem_wd2; intros.
  rewrite (Mem.nextblock_store _ _ _ _ _ _ ST).
  erewrite Mem.store_mem_contents by eauto.
  destruct (eq_dec b0 b); [subst; rewrite PMap.gss | rewrite PMap.gso; auto].
  replace ofs0 with (ofs0 + 0) at 2 by apply Z.add_0_r.
  replace ofs with (ofs + 0) at 2 by apply Z.add_0_r.
  apply Mem.setN_inj with (access := fun _ => True); intros; rewrite ?Z.add_0_r; auto.
  apply encode_val_inject.
  destruct v; try solve [constructor].
  econstructor; [|symmetry; apply Ptrofs.add_zero].
  eapply flatinj_I; auto.
Qed.

(*
Lemma mem_wd2_storebytes: forall m b ofs m' bl (WDm: mem_wd2 m)
  (ST: Mem.storebytes m b ofs bl = Some m')
  (V: val_valid v m), mem_wd2 m'.
Proof.
  unfold mem_wd2; intros.
  rewrite (Mem.nextblock_storebytes _ _ _ _ _ ST).
  erewrite Mem.storebytes_mem_contents by eauto.
  destruct (eq_dec b0 b); [subst; rewrite PMap.gss | rewrite PMap.gso; auto].
  replace ofs0 with (ofs0 + 0) at 2 by apply Z.add_0_r.
  replace ofs with (ofs + 0) at 2 by apply Z.add_0_r.
  apply Mem.setN_inj with (access := fun _ => True); intros; rewrite ?Z.add_0_r; auto.
  apply encode_val_inject.
  destruct v; try solve [constructor].
  econstructor; [|symmetry; apply Ptrofs.add_zero].
  eapply flatinj_I; auto.
Qed.
*)

Import FunInd.

Definition mem_wd' m m' := forall b ofs, memval_inject (Mem.flat_inj (Mem.nextblock m))
    (ZMap.get ofs (PMap.get b (Mem.mem_contents m'))) (ZMap.get ofs (PMap.get b (Mem.mem_contents m'))).

Lemma mem_wd'_store: forall m0 m b ofs v m' chunk (WDm: mem_wd' m0 m)
  (ST: Mem.store chunk m b ofs v = Some m')
  (V: val_valid v m0), mem_wd' m0 m'.
Proof.
  unfold mem_wd'; intros.
  erewrite Mem.store_mem_contents by eauto.
  destruct (eq_dec b0 b); [subst; rewrite PMap.gss | rewrite PMap.gso; auto].
  replace ofs0 with (ofs0 + 0) at 2 by apply Z.add_0_r.
  replace ofs with (ofs + 0) at 2 by apply Z.add_0_r.
  apply Mem.setN_inj with (access := fun _ => True); intros; rewrite ?Z.add_0_r; auto.
  apply encode_val_inject.
  destruct v; try solve [constructor].
  econstructor; [|symmetry; apply Ptrofs.add_zero].
  eapply flatinj_I; auto.
Qed.

Lemma mem_wd'_store_zeros: forall m0 m b p n m1
    (STORE_ZERO: store_zeros m b p n = Some m1) (WD: mem_wd' m0 m), mem_wd' m0 m1.
Proof. intros until n. functional induction (store_zeros m b p n); intros.
  inv STORE_ZERO; tauto.
  apply (IHo _ STORE_ZERO); clear IHo.
      eapply (mem_wd'_store m0 m). apply WD. apply e0. simpl; trivial.
  inv STORE_ZERO.
Qed.

Lemma mem_wd'_store_init_data: forall {F V} (ge: Genv.t F V) a (b:block) (z:Z)
  m m1 m2 (SID:Genv.store_init_data ge m1 b z a = Some m2),
  valid_genv ge m -> mem_wd' m m1 -> mem_wd' m m2.
Proof. intros F V ge a.
  destruct a; simpl; intros;
      try apply (mem_wd'_store _ _ _ _ _ _ _ H0 SID); simpl; trivial.
   inv SID; trivial.
   remember (Genv.find_symbol ge i) as d.
     destruct d; inv SID.
     eapply (mem_wd'_store _ _ _ _ _ _ _ H0 H2).
    apply eq_sym in Heqd.
    destruct H.
    apply v.
    unfold isGlobalBlock.
    rewrite orb_true_iff.
    unfold genv2blocksBool; simpl.
    apply Genv.find_invert_symbol in Heqd.
    rewrite Heqd; left; auto.
Qed.

Lemma mem_wd'_store_init_datalist: forall {F V} (ge: Genv.t F V) l (b:block)
  (z:Z) m m1 m2 (SID: Genv.store_init_data_list ge m1 b z l = Some m2),
  valid_genv ge m -> mem_wd' m m1 -> mem_wd' m m2.
Proof. intros F V ge l.
  induction l; simpl; intros.
    inv SID. trivial.
  remember (Genv.store_init_data ge m1 b z a) as d.
  destruct d; inv SID; apply eq_sym in Heqd.
  apply (IHl _ _ _ _ _ H2); auto; clear IHl H2.
  eapply mem_wd'_store_init_data. apply Heqd. apply H. apply H0.
Qed.

Lemma mem_wd'_alloc: forall m0 m b lo hi m' (ALL: Mem.alloc m lo hi = (m',b))
     (WDm: mem_wd' m0 m), mem_wd' m0 m'.
Proof.
  unfold mem_wd'; intros.
  destruct (eq_dec b0 b); [subst; erewrite AllocContentsUndef by eauto | erewrite AllocContentsOther by eauto; auto].
  rewrite ZMap.gi; constructor.
Qed.

Lemma mem_wd'_drop: forall m0 m b lo hi p m' (DROP: Mem.drop_perm m b lo hi p = Some m')
     (WDm: mem_wd' m0 m), mem_wd' m0 m'.
Proof.
  unfold mem_wd'; intros.
  unfold Mem.drop_perm in DROP.
  destruct (Mem.range_perm_dec _ _ _ _ _ _); inv DROP; auto.
Qed.

Lemma mem_wd'_alloc_global: forall  {F V} (ge: Genv.t F V) a m m0 m1
   (GA: Genv.alloc_global ge m0 a = Some m1),
   mem_wd' m m0 -> valid_genv ge m -> mem_wd' m m1.
Proof. intros F V ge a.
destruct a; simpl. intros.
destruct g.
  remember (Mem.alloc m0 0 1) as mm. destruct mm.
    apply eq_sym in Heqmm.
    specialize (mem_wd'_alloc _ _ _ _ _ _ Heqmm H). intros.
     eapply (mem_wd'_drop _ _ _ _ _  _ _ GA); auto.
remember (Mem.alloc m0 0 (init_data_list_size (AST.gvar_init v)) ) as mm.
  destruct mm. apply eq_sym in Heqmm.
  remember (store_zeros m2 b 0 (init_data_list_size (AST.gvar_init v)))
           as d.
  destruct d; inv GA; apply eq_sym in Heqd.
  remember (Genv.store_init_data_list ge m3 b 0 (AST.gvar_init v)) as dd.
  destruct dd; inv H2; apply eq_sym in Heqdd.
  eapply (mem_wd'_drop _ _ _ _ _ _ _ H3); clear H3.
    eapply (mem_wd'_store_init_datalist _ _ _ _ _ _ _ Heqdd); auto.
  apply (mem_wd'_store_zeros _ _ _ _ _ _ Heqd).
    apply (mem_wd'_alloc _ _ _ _ _ _ Heqmm H).
Qed.

Lemma mem_wd2_alloc_globals:
   forall F V (ge: Genv.t F V) init_list m0 m
   (GA: Genv.alloc_globals ge m0 init_list = Some m),
   mem_wd' m m0 -> valid_genv ge m -> mem_wd2 m.
Proof. intros F V ge l.
induction l; intros; simpl in *.
  inv GA. assumption.
destruct (Genv.alloc_global ge m0 a) eqn: Halloc; [|discriminate].
eapply IHl; eauto.
apply (mem_wd'_alloc_global ge _ _ _ _ Halloc H H0).
Qed.
