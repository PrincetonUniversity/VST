Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.AST.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.

Require Import VST.msl.Extensionality.

Require Import VST.sepcomp.Address.

Notation val_inject:= Val.inject.

Lemma valid_block_dec: forall m b, {Mem.valid_block m b} +  {~Mem.valid_block m b}.
Proof. intros.
unfold Mem.valid_block.
remember (plt b (Mem.nextblock m)).
destruct s. left; assumption.
right. intros N. xomega.
Qed.

Lemma Forall2_length {A B} {f:A -> B -> Prop} {l1 l2} (F:Forall2 f l1 l2): length l1 = length l2.
Proof. induction F; trivial. simpl; rewrite IHF. trivial. Qed.

Lemma Forall2_Zlength {A B} {f:A -> B -> Prop} {l1 l2} (F:Forall2 f l1 l2): Zlength l1 = Zlength l2.
Proof. do 2 rewrite Zlength_correct. rewrite (Forall2_length F). trivial. Qed.

Lemma pos_succ_plus_assoc: forall n m,
    (Pos.succ n + m = n + Pos.succ m)%positive.
Proof. intros.
  do 2 rewrite Pplus_one_succ_r;
           rewrite (Pos.add_comm m);
           rewrite Pos.add_assoc; trivial.
Qed.

Lemma mem_unchanged_on_sub: forall (P Q: block -> BinInt.Z -> Prop) m m',
  Mem.unchanged_on Q m m' ->
  (forall b ofs, P b ofs -> Q b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
intros until m'; intros [L H1 H2] H3.
split; intros.
auto.
solve[apply (H1 b ofs k p (H3 b ofs H)); auto].
solve[apply (H2 b ofs); auto].
Qed.

Lemma mem_unchanged_on_sub_strong: forall (P Q: block -> BinInt.Z -> Prop) m m',
  Mem.unchanged_on Q m m' ->
  (forall b ofs, Mem.valid_block m b -> P b ofs -> Q b ofs) ->
  Mem.unchanged_on P m m'.
Proof.
intros until m'; intros [L H1 H2] H3.
split; intros. auto.
solve[apply (H1 b ofs k p (H3 b ofs H0 H) H0)].
apply (H2 b ofs); auto. apply H3; auto.
solve[eapply Mem.perm_valid_block; eauto].
Qed.

Lemma inject_separated_same_meminj: forall j m m',
  Events.inject_separated j j m m'.
Proof. intros j m m' b; intros. congruence. Qed.

Lemma compose_meminj_idR: forall j, j = compose_meminj j inject_id.
Proof. intros. unfold  compose_meminj, inject_id.
   apply extensionality. intro b.
   remember (j b).
   destruct o; trivial. destruct p. rewrite Zplus_0_r. trivial.
Qed.

Lemma compose_meminj_idL: forall j, j = compose_meminj inject_id j.
Proof. intros. unfold  compose_meminj, inject_id.
   apply extensionality. intro b.
   remember (j b).
   destruct o; trivial. destruct p. rewrite Zplus_0_l. trivial.
Qed.

Theorem drop_extends:
  forall m1 m2 lo hi b p m1',
  Mem.extends m1 m2 ->
  Mem.drop_perm m1 b lo hi p = Some m1'  ->
  exists m2',
     Mem.drop_perm m2 b lo hi p = Some m2'
  /\ Mem.extends m1' m2'.
Proof.
  intros. inv H.
  destruct (Mem.drop_mapped_inj  _ _ _ b b 0 _ _ _ _ mext_inj H0) as [m2' [D Inj]].
        intros b'; intros. inv H1. inv H2. left. assumption.
         reflexivity.
  repeat rewrite Zplus_0_r in D. exists m2'. split; trivial.
  split; trivial.
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ H0).
  rewrite (Mem.nextblock_drop _ _ _ _ _ _ D). assumption.
(*perm_inv*)
  intros. specialize (Mem.perm_drop_4 _ _ _ _ _ _ D _ _ _ _ H); intros.
  destruct (mext_perm_inv _ _ _ _ H1).
  + left.
    destruct (eq_block b0 b); subst.
    - destruct (zle lo ofs).
      * destruct (zlt ofs hi).
        { eapply Mem.perm_implies.
            eapply Mem.perm_drop_1. eassumption. omega.
          eapply (Mem.perm_drop_2 _ _ _ _ _ _ D). 2: eassumption. omega. }
        { eapply Mem.perm_drop_3; try eassumption. right. omega. }
      * eapply Mem.perm_drop_3; try eassumption. right. omega.
    - eapply Mem.perm_drop_3; try eassumption. left; trivial.
  + right. intros N. elim H2; clear H2.
    eapply Mem.perm_drop_4; eassumption.
Qed.

Lemma mem_inj_id_trans: forall m1 m2 (Inj12: Mem.mem_inj inject_id m1 m2) m3
          (Inj23: Mem.mem_inj inject_id m2 m3),Mem.mem_inj inject_id m1 m3.
Proof. intros.
  destruct Inj12. rename mi_perm into perm12. rename mi_align into align12.
  rename mi_memval into memval12.
  destruct Inj23. rename mi_perm into perm23. rename mi_align into align23.
  rename mi_memval into memval23.
  split; intros.
  (*mi_perm*)
  apply (perm12 _ _ _ _  _ _ H) in H0.
  assert (inject_id b2 = Some (b2, delta)).
  unfold inject_id in *. inv H. trivial.
  apply (perm23 _ _ _ _  _ _ H1) in H0.  inv H. inv H1. rewrite Zplus_0_r in H0.
  assumption.
  (*mi_align*)
  apply (align12 _ _ _ _  _ _ H) in H0.
  assert (inject_id b2 = Some (b2, delta)).
  unfold inject_id in *. inv H. trivial. assumption.
  (*mi_memval*)
  assert (MV1:= memval12 _ _ _ _  H H0).
  assert (inject_id b2 = Some (b2, delta)).
  unfold inject_id in *. inv H. trivial.
  assert (R2: Mem.perm m2 b2 ofs Cur Readable).
  apply (perm12 _ _ _ _  _ _ H) in H0. inv H. rewrite Zplus_0_r in H0.
  assumption.
  assert (MV2:= memval23 _ _ _ _  H1 R2).
  inv H. inv H1.  rewrite Zplus_0_r in *.
  remember  (ZMap.get ofs (PMap.get b2 (Mem.mem_contents m2))) as v.
  destruct v. inv MV1. apply MV2.
  inv MV1. apply MV2.
  inv MV2. constructor.
  inv MV1; try solve[constructor]. inv MV2; constructor.
    specialize (val_inject_compose _ _ _ _ _ H2 H3).
    rewrite <- compose_meminj_idL; trivial.
  Qed.

Lemma extends_trans: forall m1 m2
  (Ext12: Mem.extends m1 m2) m3 (Ext23: Mem.extends m2 m3), Mem.extends m1 m3.
Proof. intros. inv Ext12. inv Ext23.
  split. rewrite mext_next. assumption. eapply mem_inj_id_trans; eauto.
(*perm_inv*)
  intros. destruct (mext_perm_inv0 _ _ _ _ H).
  + apply (mext_perm_inv _ _ _ _ H0).
  + right. intros N. elim H0; clear H0.
    specialize (Mem.mi_perm _ _ _ mext_inj b b 0 ofs Max Nonempty); intros.
    rewrite Zplus_0_r in H0; apply H0; trivial.
Qed.

Lemma memval_inject_id_refl: forall v, memval_inject inject_id v v.
Proof.
  destruct v. constructor. constructor. econstructor.
  destruct v; try econstructor. reflexivity. rewrite Ptrofs.add_zero. trivial.
Qed.

Lemma extends_refl: forall m, Mem.extends m m.
Proof. intros.
  split. trivial.
  split; intros.
     inv H.  rewrite Zplus_0_r. assumption.
     inv H. apply Z.divide_0_r. (*rewrite Zplus_0_r. assumption.*)
     inv H.  rewrite Zplus_0_r. apply memval_inject_id_refl.
(*perm_inv*)
  intros. left; trivial.
Qed.

Lemma perm_decE:
  forall m b ofs k p PF,
  (Mem.perm_dec m b ofs k p = left PF <-> Mem.perm m b ofs k p).
Proof.
intros until p.
split; auto.
intros H1.
destruct (Mem.perm_dec m b ofs k p).
solve[f_equal; apply proof_irr].
solve[elimtype False; auto].
Qed.

Lemma flatinj_E: forall b b1 b2 delta (H:Mem.flat_inj b b1 = Some (b2, delta)),
  b2=b1 /\ delta=0 /\ Plt b2 b.
Proof.
  unfold Mem.flat_inj. intros.
  destruct (plt b1 b); inv H. repeat split; trivial.
Qed.

Lemma flatinj_I: forall bb b, Plt b bb -> Mem.flat_inj bb b = Some (b, 0).
Proof.
  intros. unfold Mem.flat_inj.
  destruct (plt b bb); trivial. exfalso. xomega.
Qed.

Lemma flatinj_mono: forall b b1 b2 b' delta
  (F: Mem.flat_inj b1 b = Some (b', delta)),
  Plt b1 b2 -> Mem.flat_inj b2 b = Some (b', delta).
Proof. intros.
  apply flatinj_E in F. destruct F as [? [? ?]]; subst.
  apply flatinj_I. xomega.
Qed.

(* A minimal preservation property we sometimes require. *)
(*
Definition readonly {F V} (ge: Genv.t F V) m1 b m2 :=
    forall gv, Genv.find_var_info ge b = Some gv ->
       gvar_readonly gv && negb (gvar_volatile gv) = true ->
    forall ch ofs, Mem.load ch m2 b ofs = Mem.load ch m1 b ofs.
*)

Definition readonlyLD m1 b m2 :=
    forall chunk ofs
    (NWR: forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
                          ~(Mem.perm m1 b ofs' Cur Writable)),
     Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs /\
     (forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
        (forall k p, Mem.perm m1 b ofs' k p <-> Mem.perm m2 b ofs' k p)).

Definition readonly m1 b m2 :=
    forall n ofs
    (NWR: forall i, 0 <= i < n ->
                          ~(Mem.perm m1 b (ofs + i) Cur Writable)),
     Mem.loadbytes m2 b ofs n = Mem.loadbytes m1 b ofs n /\
     (forall i, 0 <= i < n ->
        (forall k p, Mem.perm m1 b (ofs+i) k p <-> Mem.perm m2 b (ofs+i) k p)).

Definition max_readonlyLD m1 b m2 :=
    forall chunk ofs
    (NWR: forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
                          ~(Mem.perm m1 b ofs' Max Writable)),
     Mem.load chunk m2 b ofs = Mem.load chunk m1 b ofs /\
     (forall ofs', ofs <= ofs' < ofs + size_chunk chunk ->
        (forall k p, Mem.perm m1 b ofs' k p <-> Mem.perm m2 b ofs' k p)).

Definition max_readonly m1 b m2 :=
    forall n ofs
    (NWR: forall i, 0 <= i < n ->
                          ~(Mem.perm m1 b (ofs + i) Max Writable)),
     Mem.loadbytes m2 b ofs n = Mem.loadbytes m1 b ofs n /\
     (forall i, 0 <= i < n ->
        (forall k p, Mem.perm m1 b (ofs+i) k p <-> Mem.perm m2 b (ofs+i) k p)).

Lemma readonlyLD_max_readonlyLD m1 b m2: readonlyLD m1 b m2 -> max_readonlyLD m1 b m2.
Proof. red; intros. destruct (H chunk ofs).
  intros; intros N. apply Mem.perm_max in N. apply (NWR _ H0 N).
  split; trivial.
Qed.

Lemma readonly_max_readonly m1 b m2: readonly m1 b m2 -> max_readonly m1 b m2.
Proof. red; intros. destruct (H n ofs).
  intros; intros N. apply Mem.perm_max in N. apply (NWR _ H0 N).
  split; trivial.
Qed.

Lemma readonly_readonlyLD m1 b m2: readonly m1 b m2 -> readonlyLD m1 b m2.
Proof.
  red; intros. destruct (H (size_chunk chunk) ofs); clear H.
    intros. apply NWR. omega.
  split; intros.
    remember (Mem.load chunk m2 b ofs) as d; symmetry in Heqd; symmetry.
    destruct d.
    { destruct (Mem.load_loadbytes _ _ _ _ _ Heqd) as [bytes [LDB V]]; subst v.
      apply Mem.load_valid_access in Heqd; destruct Heqd.
      rewrite H0 in LDB. apply Mem.loadbytes_load; trivial.
    }
    { remember (Mem.load chunk m1 b ofs) as q; symmetry in Heqq; symmetry.
      destruct q; trivial.
      destruct (Mem.load_loadbytes _ _ _ _ _ Heqq) as [bytes [LDB V]]; subst v.
      apply Mem.load_valid_access in Heqq; destruct Heqq.
      rewrite <- Heqd.
      rewrite <- H0 in LDB. apply Mem.loadbytes_load; trivial. }
  specialize (H1 (ofs'-ofs)). rewrite Zplus_minus in H1. apply H1. omega.
Qed.

Lemma readonly_refl m b: readonly m b m.
  Proof. red; intuition. Qed.

Lemma readonlyLD_refl m b: readonlyLD m b m.
  Proof. red; intuition. Qed.

Lemma readonlyLD_trans m1 m2 m3 b: readonlyLD m1 b m2 -> readonlyLD m2 b m3 -> readonlyLD m1 b m3.
  Proof. red; intros. destruct (H _ _ NWR); clear H.
    destruct (H0 chunk ofs); clear H0.
      intros. intros N. apply (NWR _ H). apply (H2 _ H). assumption.
    split. rewrite <- H1. assumption.
    intros. destruct (H2 _ H0 k p); clear H2. destruct (H3 _ H0 k p); clear H3.
      split; eauto.
  Qed.

Lemma readonly_trans m1 m2 m3 b: readonly m1 b m2 -> readonly m2 b m3 -> readonly m1 b m3.
  Proof. red; intros. destruct (H _ _ NWR); clear H.
    destruct (H0 n ofs); clear H0.
      intros. intros N. apply (NWR _ H). apply (H2 _ H). assumption.
    split. rewrite <- H1. assumption.
    intros. destruct (H2 _ H0 k p); clear H2. destruct (H3 _ H0 k p); clear H3.
      split; eauto.
  Qed.

Definition mem_forward (m1 m2:mem) :=
  forall b, Mem.valid_block m1 b ->
    (Mem.valid_block m2 b
     /\ (forall ofs p, Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p)
     (*/\ readonly m1 b m2*)).

Lemma mem_forward_refl: forall m, mem_forward m m.
Proof. intros m b H. split; trivial.
(*  split; eauto. apply readonly_refl.*)
Qed.

Lemma mem_forward_trans: forall m1 m2 m3,
  mem_forward m1 m2 -> mem_forward m2 m3 -> mem_forward m1 m3.
Proof. intros. intros  b Hb.
  destruct (H _ Hb) as [? ?].
  destruct (H0 _ H1) as [? ?].
  split; eauto.
Qed.

Lemma forward_unchanged_trans: forall P m1 m2 m3,
Mem.unchanged_on P m1 m2 -> Mem.unchanged_on P m2 m3 ->
mem_forward m1 m2 -> mem_forward m2 m3 ->
mem_forward m1 m3 /\ Mem.unchanged_on P m1 m3.
Proof. intros.
split. eapply mem_forward_trans; eassumption.
split; intros.
  eapply Ple_trans; eapply Mem.unchanged_on_nextblock; eassumption.
  destruct H.
  destruct (unchanged_on_perm _ _ k p H3 H4).
  destruct H0. destruct (H1 _ H4).
  destruct (unchanged_on_perm0 _ _ k p H3 H0).
  split; intros; auto.
destruct H.
  rewrite <- (unchanged_on_contents _ _ H3 H4).
  destruct H0.
  apply (unchanged_on_contents0 _ _ H3).
  apply unchanged_on_perm; try assumption.
  apply Mem.perm_valid_block in H4. assumption.
Qed.

Lemma matchOptE: forall {A} (a:option A) (P: A -> Prop),
   match a with Some b => P b | None => False end ->
   exists b, a = Some b /\ P b.
Proof. intros. destruct a; try contradiction. exists a; auto. Qed.

Lemma compose_meminjD_None: forall j jj b,
  (compose_meminj j jj) b = None ->
  j b = None \/
  (exists b', exists ofs, j b = Some(b',ofs) /\ jj b' = None).
Proof.
  unfold compose_meminj; intros.
  destruct (j b).
  destruct p. right.
  remember (jj b0) as zz; destruct zz. destruct p. inv H.
  exists b0. exists z. rewrite <- Heqzz. auto.
  left; trivial.
Qed.

Lemma compose_meminjD_Some: forall j jj b b2 ofs2,
       (compose_meminj j jj) b = Some(b2,ofs2) ->
       exists b1, exists ofs1, exists ofs,
       j b = Some(b1,ofs1) /\ jj b1 = Some(b2,ofs) /\ ofs2=ofs1+ofs.
Proof. unfold compose_meminj; intros.
       remember (j b) as z; destruct z; apply eq_sym in Heqz.
         destruct p. exists b0. exists z.
         remember (jj b0) as zz.
         destruct zz; apply eq_sym in Heqzz.
           destruct p. inv H. exists z0. auto.
           inv H.
         inv H.
Qed.

Lemma compose_meminj_inject_incr: forall j12 j12' j23 j23'
  (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23'),
  inject_incr (compose_meminj j12 j23) (compose_meminj j12' j23').
Proof.
  intros. intros b; intros.
  apply compose_meminjD_Some in H.
  destruct H as [b1 [ofs1 [ofs [Hb [Hb1 Hdelta]]]]].
  unfold compose_meminj.
  rewrite (InjIncr12 _ _ _ Hb).
  rewrite (InjIncr23 _ _ _ Hb1). subst. trivial.
Qed.

Lemma compose_meminj_inject_separated: forall j12 j12' j23 j23' m1 m2 m3
   (InjSep12 : inject_separated j12 j12' m1 m2)
   (InjSep23 : inject_separated j23 j23' m2 m3)
   (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23')
   (BV12: forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
   (BV23: forall b1 b2 ofs, j23 b1 = Some (b2,ofs) -> Mem.valid_block m2 b1 /\ Mem.valid_block m3 b2),
   inject_separated (compose_meminj j12 j23) (compose_meminj j12' j23') m1 m3.
Proof. intros.
  unfold compose_meminj; intros b; intros.
  remember (j12 b) as j12b.
  destruct j12b; inv H; apply eq_sym in Heqj12b. destruct p.
    rewrite (InjIncr12 _ _ _ Heqj12b) in H0.
    remember (j23 b0) as j23b0.
    destruct j23b0; inv H2; apply eq_sym in Heqj23b0. destruct p. inv H1.
    remember (j23' b0) as j23'b0.
    destruct j23'b0; inv H0; apply eq_sym in Heqj23'b0. destruct p. inv H1.
    destruct (InjSep23 _ _ _ Heqj23b0 Heqj23'b0).
    split; trivial. exfalso. apply H. eapply BV12. apply Heqj12b.
  remember (j12' b) as j12'b.
  destruct j12'b; inv H0; apply eq_sym in Heqj12'b. destruct p.
    destruct (InjSep12 _ _ _ Heqj12b Heqj12'b). split; trivial.
    remember (j23' b0) as j23'b0.
    destruct j23'b0; inv H1; apply eq_sym in Heqj23'b0. destruct p. inv H3.
    remember (j23 b0) as j23b0.
    destruct j23b0; apply eq_sym in Heqj23b0. destruct p.
      rewrite (InjIncr23 _ _ _ Heqj23b0) in Heqj23'b0. inv Heqj23'b0.
      exfalso. apply H0. eapply BV23. apply Heqj23b0.
    destruct (InjSep23 _ _ _ Heqj23b0 Heqj23'b0). assumption.
Qed.

Lemma compose_meminj_inject_separated': forall j12 j12' j23 j23' m1 m2 m3
   (InjSep12 : inject_separated j12 j12' m1 m2)
   (InjSep23 : inject_separated j23 j23' m2 m3)
   (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23')
   (MInj12: Mem.inject j12 m1 m2)
   (MInj23: Mem.inject j23 m2 m3),
   inject_separated (compose_meminj j12 j23) (compose_meminj j12' j23') m1 m3.
Proof. intros.
  eapply compose_meminj_inject_separated; try eassumption.
  intros; split. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12).
    apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  intros; split. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23).
    apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj23).
Qed.

Lemma forall_lessdef_refl: forall vals,  Forall2 Val.lessdef vals vals.
Proof. induction vals; econstructor; trivial. Qed.

Lemma lessdef_hastype: forall v v' (V:Val.lessdef v v') T,
              Val.has_type v' T -> Val.has_type v T.
Proof. intros. inv V; simpl; trivial. Qed.

Lemma forall_lessdef_hastype: forall vals vals'
          (V:Forall2 Val.lessdef vals vals') Ts
          (HTs: Forall2 Val.has_type vals' Ts),
          Forall2 Val.has_type vals Ts.
Proof.
  intros vals vals' V.
  induction V; simpl in *; intros.
       trivial.
  inv HTs. constructor. eapply  lessdef_hastype; eassumption. apply (IHV _ H4).
Qed.

Lemma valinject_hastype:  forall j v v'
       (V: (val_inject j) v v') T,
       Val.has_type v' T -> Val.has_type v T.
Proof. intros. inv V; simpl; trivial. Qed.

Lemma forall_valinject_hastype:  forall j vals vals'
            (V:  Forall2 (val_inject j) vals vals')
            Ts (HTs: Forall2 Val.has_type vals' Ts),
            Forall2 Val.has_type vals Ts.
Proof.
  intros j vals vals' V.
  induction V; simpl in *; intros.
       trivial.
  inv HTs. constructor. eapply  valinject_hastype; eassumption. apply (IHV _ H4).
Qed.

Definition val_inject_opt (j: meminj) (v1 v2: option val) :=
  match v1, v2 with Some v1', Some v2' => val_inject j v1' v2'
  | None, None => True
  | _, _ => False
  end.

Lemma val_inject_split:
  forall v1 v3 j12 j23 (V: val_inject (compose_meminj j12 j23) v1 v3),
    exists v2, val_inject j12 v1 v2 /\ val_inject j23 v2 v3.
Proof. intros.
   inv V.
     exists (Vint i). split; constructor.
     exists (Vlong i); split; constructor.
     exists (Vfloat f). split; constructor.
     exists (Vsingle f). split; constructor.
     apply compose_meminjD_Some in H. rename b2 into b3.
       destruct H as [b2 [ofs2 [ofs3 [J12 [J23 DD]]]]]; subst.
       eexists. split. econstructor. apply J12. reflexivity.
          econstructor. apply J23. rewrite Ptrofs.add_assoc.
          f_equal. rewrite Ptrofs.add_unsigned.
            apply Ptrofs.eqm_samerepr. 
            apply Ptrofs.eqm_add; apply Ptrofs.eqm_unsigned_repr.
     exists Vundef. split; constructor.
Qed.

Lemma forall_lessdef_trans:
  forall vals1 vals2 (V12: Forall2 Val.lessdef vals1 vals2)
    vals3  (V23: Forall2 Val.lessdef vals2 vals3),
    Forall2 Val.lessdef vals1 vals3.
Proof. intros vals1 vals2 V12.
   induction V12; intros; inv V23; econstructor.
   eapply Val.lessdef_trans; eauto.
          eapply IHV12; trivial.
Qed.

Lemma extends_loc_out_of_bounds:
  forall m1 m2 (Ext: Mem.extends m1 m2) b ofs,
    loc_out_of_bounds m2 b ofs -> loc_out_of_bounds m1 b ofs.
Proof. intros.
  inv Ext. inv mext_inj.
  intros N.  eapply H. apply (mi_perm _ b 0) in N.
    rewrite Zplus_0_r in N. assumption. reflexivity.
Qed.

Lemma extends_loc_out_of_reach:
  forall m1 m2 (Ext: Mem.extends m1 m2) b ofs j
    (Hj: loc_out_of_reach j m2 b ofs), loc_out_of_reach j m1 b ofs.
Proof.
  intros. unfold loc_out_of_reach in *. intros.
  intros N. eapply (Hj _ _ H). clear Hj H. inv Ext. inv mext_inj.
  specialize (mi_perm b0 _ 0 (ofs - delta) Max Nonempty (eq_refl _)).
    rewrite Zplus_0_r in mi_perm. apply (mi_perm N).
Qed.

Lemma valinject_lessdef:
  forall v1 v2 v3 j (V12:val_inject j v1 v2) (V23 : Val.lessdef v2 v3),
    val_inject j v1 v3.
Proof.
  intros.
  inv V12; inv V23; try constructor.
    econstructor. eassumption. trivial.
Qed.

Lemma forall_valinject_lessdef:
  forall vals1 vals2 j (VInj12 : Forall2 (val_inject j) vals1 vals2) vals3
    (LD23 : Forall2 Val.lessdef vals2 vals3), Forall2 (val_inject j) vals1 vals3.
Proof. intros vals1 vals2 j VInj12.
   induction VInj12; intros; inv LD23. constructor.
     econstructor. eapply valinject_lessdef; eassumption.
          eapply (IHVInj12 _ H4).
Qed.

Lemma val_lessdef_inject_compose:
  forall v1 v2 (LD12 : Val.lessdef v1 v2) j v3
    (InjV23 : val_inject j v2 v3), val_inject j v1 v3.
Proof. intros.
  apply val_inject_id in LD12.
  apply (val_inject_compose _ _ _ _ _ LD12) in InjV23.
  rewrite <- compose_meminj_idL in InjV23. assumption.
Qed.

Lemma forall_val_lessdef_inject_compose:
  forall v1 v2 (LD12 : Forall2 Val.lessdef v1 v2) j v3
    (InjV23 : Forall2 (val_inject j) v2 v3), Forall2 (val_inject j) v1 v3.
Proof. intros v1 v2 H.
  induction H; intros; inv InjV23; econstructor.
       eapply val_lessdef_inject_compose; eassumption.
       apply (IHForall2 _ _ H5).
Qed.

Lemma forall_val_inject_compose:
  forall vals1 vals2 j1 (ValsInj12 : Forall2 (val_inject j1) vals1 vals2)
     vals3 j2 (ValsInj23 : Forall2 (val_inject j2) vals2 vals3),
     Forall2 (val_inject (compose_meminj j1 j2)) vals1 vals3.
Proof.
  intros vals1 vals2 j1 ValsInj12.
  induction ValsInj12; intros; inv ValsInj23; econstructor.
     eapply val_inject_compose; eassumption.
  apply (IHValsInj12 _ _ H4).
Qed.

Lemma val_inject_flat:
  forall m1 m2 j (Inj: Mem.inject j m1 m2) v1 v2 (V: val_inject j v1 v2),
    val_inject  (Mem.flat_inj (Mem.nextblock m1)) v1 v1.
Proof. intros.
  inv V; try constructor.
    apply Val.inject_ptr with (delta:=0).
            unfold Mem.flat_inj. inv Inj.
            destruct (plt b1 (Mem.nextblock m1)).
               trivial.
            assert (j b1 = None).
              apply mi_freeblocks.  assumption. rewrite H in H0. inv H0.
            rewrite Ptrofs.add_zero. trivial.
Qed.

Lemma forall_val_inject_flat: forall m1 m2 j (Inj: Mem.inject j m1 m2) vals1 vals2
                (V: Forall2 (val_inject j) vals1 vals2),
                Forall2 (val_inject  (Mem.flat_inj (Mem.nextblock m1))) vals1 vals1.
Proof. intros.
  induction V; intros; try econstructor.
       eapply val_inject_flat; eassumption.
  apply IHV.
Qed.

Lemma po_trans: forall a b c, Mem.perm_order'' a b ->  Mem.perm_order'' b c ->
      Mem.perm_order'' a c.
Proof. intros.
   destruct a; destruct b; destruct c; simpl in *; try contradiction; try trivial.
   eapply perm_order_trans; eassumption.
Qed.

Lemma extends_perm: forall m1 m2 (Ext: Mem.extends m1 m2) b ofs k p,
   Mem.perm m1 b ofs k p -> Mem.perm m2 b ofs k p.
Proof. intros. destruct Ext. destruct mext_inj.
  specialize (mi_perm b b 0 ofs k p (eq_refl _) H).
  rewrite Zplus_0_r in mi_perm. assumption.
Qed.

Lemma extends_permorder: forall m1 m2 (Ext: Mem.extends m1 m2) (b:block) ofs k,
  Mem.perm_order'' (PMap.get b (Mem.mem_access m2) ofs k)
                   (PMap.get b (Mem.mem_access m1) ofs k).
Proof.
  intros. destruct Ext.  destruct mext_inj as [prm _ _].
  specialize (prm b b 0 ofs k). unfold Mem.perm in prm.
  remember ((PMap.get b (Mem.mem_access m2) ofs k)) as z.
  destruct z; apply eq_sym in Heqz; simpl  in *.
    remember ((PMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       rewrite Zplus_0_r in prm. rewrite Heqz in prm.
       specialize (prm p0 (eq_refl _)). apply prm. apply perm_refl.
  remember ((PMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       rewrite Zplus_0_r in prm. rewrite Heqz in prm.
       specialize (prm p (eq_refl _)). exfalso. apply prm. apply perm_refl.
Qed.

Lemma fwd_maxperm: forall m1 m2 (FWD: mem_forward m1 m2) b
  (V:Mem.valid_block m1 b) ofs p,
  Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Proof. intros. apply FWD; assumption. Qed.

Lemma fwd_maxpermorder: forall m1 m2 (FWD: mem_forward m1 m2) (b:block)
  (V:Mem.valid_block m1 b) ofs,
  Mem.perm_order'' (PMap.get b (Mem.mem_access m1) ofs Max)
                   (PMap.get b (Mem.mem_access m2) ofs Max).
Proof.
  intros. destruct (FWD b) as [? ?]; try assumption.
  remember ((PMap.get b (Mem.mem_access m2) ofs Max)) as z.
  destruct z; apply eq_sym in Heqz; simpl  in *.
  remember ((PMap.get b (Mem.mem_access m1) ofs Max)) as zz.
  destruct zz; apply eq_sym in Heqzz; simpl  in *.
  specialize (H0 ofs p).  unfold Mem.perm in H0. unfold Mem.perm_order' in H0.
  rewrite Heqz in H0. rewrite Heqzz in H0. apply H0. apply perm_refl.
  specialize (H0 ofs p).  unfold Mem.perm in H0. unfold Mem.perm_order' in H0.
  rewrite Heqz in H0. rewrite Heqzz in H0. apply H0. apply perm_refl.
  remember ((PMap.get b (Mem.mem_access m1) ofs Max)) as zz.
  destruct zz; apply eq_sym in Heqzz; simpl in *; trivial.
Qed.

Lemma po_oo: forall p q, Mem.perm_order' p q = Mem.perm_order'' p (Some q).
Proof. intros. destruct p; trivial. Qed.

Lemma inject_permorder:
  forall j m1 m2 (Inj : Mem.inject j m1 m2) (b b':block) ofs'
      (J: j b = Some (b', ofs')) ofs k,
    Mem.perm_order'' (PMap.get b' (Mem.mem_access m2) (ofs + ofs') k)
   (PMap.get b (Mem.mem_access m1) ofs k).
Proof.
  intros. destruct Inj. destruct mi_inj as [prm _ _ ].
  specialize (prm b b' ofs' ofs k). unfold Mem.perm in prm.
  remember ((PMap.get b' (Mem.mem_access m2) (ofs + ofs') k)) as z.
  destruct z; apply eq_sym in Heqz; simpl  in *.
    remember ((PMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       eapply prm. apply J. apply perm_refl.
  remember ((PMap.get b (Mem.mem_access m1) ofs k)) as zz.
    destruct zz; trivial; apply eq_sym in Heqzz; simpl  in *.
       eapply prm. apply J. apply perm_refl.
Qed.

Lemma PermExtNotnonempty:
  forall m1 m2
    (Inj: Mem.extends m1 m2) b ofs p
    (H: ~ Mem.perm m2 b ofs p Nonempty),
    ~Mem.perm m1 b ofs p Nonempty.
Proof. intros. destruct Inj. destruct mext_inj.
intros N. apply H. apply (mi_perm _ _ _ _ _ _ (eq_refl _)) in N.
  rewrite Zplus_0_r in N. apply N.
Qed.

Lemma PermInjNotnonempty:
  forall j m1 m2
    (Inj: Mem.inject j m1 m2) b b2 delta (J:j b = Some(b2,delta)) ofs p
    (H: ~Mem.perm m2 b2 (ofs+delta) p Nonempty),
    ~Mem.perm m1 b ofs p Nonempty.
Proof. intros. destruct Inj. destruct mi_inj.
intros N. apply H. apply (mi_perm _ _ _ _ _ _ J) in N. apply N.
Qed.

Lemma inject_LOOR_LOOB:
  forall m1 m2 j (Minj12 : Mem.inject j m1 m2) m3 m3',
  Mem.unchanged_on (loc_out_of_reach j m1) m3 m3' ->
  Mem.unchanged_on (loc_out_of_bounds m2) m3 m3'.
Proof. intros.
    split; intros; eapply H; trivial.
         intros b2; intros.
           unfold loc_out_of_bounds in H0. intros N. apply H0.
           inv Minj12. inv mi_inj. apply (mi_perm _ _ _ _ _ _ H2) in N.
           rewrite <- Zplus_comm in N. rewrite Zplus_minus in N.  apply N.
    intros b2; intros. unfold loc_out_of_bounds in H0. intros N. apply H0.
           inv Minj12. inv mi_inj. apply (mi_perm _ _ _ _ _ _ H2) in N.
           rewrite <- Zplus_comm in N. rewrite Zplus_minus in N.  apply N.
Qed.

Lemma free_neutral:
  forall (thr : block) (m : mem) (lo hi : Z) (b : block) (m' : Mem.mem')
  (FREE: Mem.free m b lo hi = Some m'),
  Mem.inject_neutral thr m -> Mem.inject_neutral thr m'.
Proof. intros. inv H.
  split; intros.
     apply flatinj_E in H. destruct H as [? [? ?]]; subst.
       rewrite Zplus_0_r. assumption.
     apply flatinj_E in H. destruct H as [? [? ?]]; subst.
       apply Z.divide_0_r.
     apply flatinj_E in H. destruct H as [? [? ?]]; subst.
       rewrite Zplus_0_r.
       assert (X: Mem.flat_inj thr b1 = Some (b1,0)).
         { apply flatinj_I. assumption. }
       assert (Y:= Mem.perm_free_3 _ _ _ _ _ FREE _ _ _ _ H0).
        specialize (mi_memval _ _ _ _ X Y). rewrite Zplus_0_r in *.
        rewrite (Mem.free_result _ _ _ _ _ FREE) in *. simpl in *.
          apply mi_memval.
Qed.

Lemma getN_aux: forall n p c B1 v B2, Mem.getN n p c = B1 ++ v::B2 ->
    v = ZMap.get (p + Z.of_nat (length B1)) c.
Proof. intros n.
  induction n; simpl; intros.
    destruct B1; simpl in *. inv H. inv H.
    destruct B1; simpl in *.
      inv H. rewrite Zplus_0_r. trivial.
      inv H. specialize (IHn _ _ _ _ _ H2). subst.
        rewrite Zpos_P_of_succ_nat.
        remember (Z.of_nat (length B1)) as m. clear Heqm H2. rewrite <- Z.add_1_l.
         rewrite Zplus_assoc. trivial.
Qed.

Lemma getN_range: forall n ofs M bytes1 v bytes2,
  Mem.getN n ofs M = bytes1 ++ v::bytes2 ->
  (length bytes1 < n)%nat.
Proof. intros n.
  induction n; simpl; intros.
    destruct bytes1; inv H.
    destruct bytes1; simpl in *; inv H.
      omega.
    specialize (IHn _ _ _ _ _ H2). omega.
Qed.

Lemma loadbytes_D: forall m b ofs n bytes
      (LD: Mem.loadbytes m b ofs n = Some bytes),
      Mem.range_perm m b ofs (ofs + n) Cur Readable /\
      bytes = Mem.getN (nat_of_Z n) ofs (PMap.get b (Mem.mem_contents m)).
Proof. intros.
  Transparent Mem.loadbytes.
  unfold Mem.loadbytes in LD.
  Opaque Mem.loadbytes.
  remember (Mem.range_perm_dec m b ofs (ofs + n) Cur Readable) as d.
  destruct d; inv LD. auto.
Qed.

(*A new lemma, used in CompCert2.5 where CompComp-4-CompCert2.1 used decode_val_pointer_inv*)
Lemma load_ptr_is_fragment ch m b ofs b0 i
      (LD: Mem.load ch m b ofs = Some (Vptr b0 i)):
  exists q n, ZMap.get ofs (Mem.mem_contents m) !! b = Fragment (Vptr b0 i) q n.
Proof.
  apply Mem.load_result in LD.
  apply eq_sym in LD.
  unfold decode_val in LD.
  remember (proj_bytes
         (Mem.getN (size_chunk_nat ch) ofs (Mem.mem_contents m) !! b)) as v.
  destruct v.
  + destruct ch; inv LD.
  + destruct ch; try solve [inv LD].
    - unfold Val.load_result in LD. unfold proj_bytes in Heqv. simpl in *.
      remember (ZMap.get ofs (Mem.mem_contents m) !! b) as w.
      destruct w; try discriminate. clear Heqv.
      destruct (Val.eq v v); try discriminate.
      destruct q; try discriminate. simpl in *.
      destruct Archi.ptr64 eqn:Hp; try discriminate LD.
      repeat (
        rewrite proj_sumbool_is_true in LD by auto;
        simpl in LD;
        repeat (destruct n; simpl in LD; try discriminate; [idtac]);
        match type of LD with context [ZMap.get ?X _ !! _] =>
          destruct (ZMap.get X (Mem.mem_contents m) !! b); try discriminate LD; [idtac]
        end;
        destruct (Val.eq v v0); try discriminate LD; subst v0;
        destruct q; simpl in LD; try discriminate; [idtac]).
        rewrite proj_sumbool_is_true in LD by auto.
       simpl in LD.
       destruct n; simpl in LD; try discriminate; [idtac].
       destruct v; inv LD. eauto.
    - unfold Val.load_result in LD. unfold proj_bytes in Heqv. simpl in *.
      remember (ZMap.get ofs (Mem.mem_contents m) !! b) as w.
      destruct w; try discriminate. clear Heqv.
      destruct (Val.eq v v); try discriminate.
      destruct q; try discriminate. simpl in *.
      repeat (
        rewrite proj_sumbool_is_true in LD by auto;
        simpl in LD;
        repeat (destruct n; simpl in LD; try discriminate; [idtac]);
        match type of LD with context [ZMap.get ?X _ !! _] =>
          destruct (ZMap.get X (Mem.mem_contents m) !! b); try discriminate LD; [idtac]
        end;
        destruct (Val.eq v v0); try discriminate LD; subst v0;
        destruct q; simpl in LD; try discriminate; [idtac]).
        rewrite proj_sumbool_is_true in LD by auto.
       simpl in LD.
       destruct n; simpl in LD; try discriminate; [idtac].
       destruct v; inv LD;
      destruct Archi.ptr64 eqn:Hp; try discriminate LD; eauto.
    - unfold Val.load_result in LD. unfold proj_bytes in Heqv. simpl in *.
      remember (ZMap.get ofs (Mem.mem_contents m) !! b) as w.
      destruct w; try discriminate. clear Heqv.
        rewrite ?proj_sumbool_is_true in LD by auto.
        destruct q; simpl in LD; try discriminate; [idtac].
        simpl in LD.
      repeat (
        rewrite ?proj_sumbool_is_true in LD by auto;
        simpl in LD;
        repeat (destruct n; simpl in LD; try discriminate; [idtac]);
        match type of LD with context [ZMap.get ?X _ !! _] =>
          destruct (ZMap.get X (Mem.mem_contents m) !! b); try discriminate LD; [idtac]
        end;
        destruct (Val.eq v v0); try discriminate LD; subst v0;
        destruct q; simpl in LD; try discriminate; [idtac]).
        rewrite proj_sumbool_is_true in LD by auto.
       destruct n; simpl in LD; try discriminate; [idtac].
       destruct v; inv LD. eauto.
Qed.

(******** Compatibility of memory operation with [mem_forward] ********)
Lemma load_storebytes_nil m b ofs m': Mem.storebytes m b ofs nil = Some m' ->
  forall ch bb z, Mem.load ch m' bb z = Mem.load ch m bb z.
Proof. intros.
  remember (Mem.load ch m' bb z) as u'; symmetry in Hequ'; destruct u'.
      symmetry.
      eapply Mem.load_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Pos.le_refl.
        split; intros.
          eapply Mem.perm_storebytes_2; eassumption.
          eapply Mem.perm_storebytes_1; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.

    remember (Mem.load ch m bb z) as u; symmetry in Hequ; destruct u; trivial.
      rewrite <- Hequ'; clear Hequ'.
      eapply Mem.load_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Pos.le_refl.
        split; intros.
          eapply Mem.perm_storebytes_1; eassumption.
          eapply Mem.perm_storebytes_2; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.
Qed.

Lemma loadbytes_storebytes_nil m b ofs m': Mem.storebytes m b ofs nil = Some m' ->
  forall n bb z, Mem.loadbytes m' bb z n = Mem.loadbytes m bb z n.
Proof. intros.
  remember (Mem.loadbytes m' bb z n) as u'; symmetry in Hequ'; destruct u'.
      symmetry.
      eapply Mem.loadbytes_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Pos.le_refl.
        split; intros.
          eapply Mem.perm_storebytes_2; eassumption.
          eapply Mem.perm_storebytes_1; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.

    remember (Mem.loadbytes m bb z n) as u; symmetry in Hequ; destruct u; trivial.
      rewrite <- Hequ'; clear Hequ'.
      eapply Mem.loadbytes_unchanged_on; try eassumption.
      instantiate (1:= fun b ofs => True).
      split; intros.
        rewrite (Mem.nextblock_storebytes _ _ _ _ _ H); apply Pos.le_refl.
        split; intros.
          eapply Mem.perm_storebytes_1; eassumption.
          eapply Mem.perm_storebytes_2; eassumption.
      rewrite (Mem.storebytes_mem_contents _ _ _ _ _ H).
      destruct (eq_block b0 b); subst. rewrite PMap.gss; trivial.
      rewrite PMap.gso; trivial.
    intros; simpl; trivial.
Qed.

Lemma storebytes_forward: forall m b ofs bytes m'
      (M: Mem.storebytes m b ofs bytes = Some m'),
      mem_forward m m'.
Proof. intros.
  split; intros.
    eapply Mem.storebytes_valid_block_1; eassumption.
    eapply Mem.perm_storebytes_2; eassumption.
Qed.

Lemma storebytes_readonlyLD: forall m b ofs bytes m'
      (M: Mem.storebytes m b ofs bytes = Some m'),
      forall b, Mem.valid_block m b -> readonlyLD m b m'.
Proof.
  red; intros.
  split.
    destruct bytes.
      eapply load_storebytes_nil; eassumption.
    eapply Mem.load_storebytes_other; try eassumption.
    destruct (eq_block b0 b); subst. 2: left; trivial. right.
    apply Mem.storebytes_range_perm in M.
    destruct (zle (ofs0 + size_chunk chunk) ofs). left; trivial. right.
    destruct (zle (ofs + Z.of_nat (length (m0 :: bytes)))  ofs0); trivial.
    exfalso.
    destruct (zle ofs0 ofs).
      apply (NWR ofs). omega.
                      (*eapply Mem.perm_max.*) apply M. simpl. specialize (Zle_0_nat (length bytes)); intros; xomega.
      elim (NWR ofs0). specialize (size_chunk_pos chunk); intros; omega.
                      (*eapply Mem.perm_max.*) apply M. omega.
  split; intros. eapply Mem.perm_storebytes_1; eassumption. eapply Mem.perm_storebytes_2; eassumption.
Qed.

Lemma storebytes_readonly: forall m b ofs bytes m'
      (M: Mem.storebytes m b ofs bytes = Some m'),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof.
  red; intros.
  destruct (zle n 0).
  { split; intros. repeat rewrite Mem.loadbytes_empty; trivial. omega. }
  split.
    destruct bytes.
      eapply loadbytes_storebytes_nil; eassumption.
    eapply Mem.loadbytes_storebytes_other; try eassumption. omega.
    destruct (eq_block b0 b); subst. 2: left; trivial. right.
    apply Mem.storebytes_range_perm in M.
    destruct (zle (ofs0 + n) ofs). left; trivial. right.
    destruct (zle (ofs + Z.of_nat (length (m0 :: bytes)))  ofs0); trivial.
    exfalso. remember (Z.of_nat (length (m0 :: bytes))) as l. assert (0 < l). simpl in Heql. xomega. clear Heql.
    destruct (zle ofs0 ofs).
      apply (NWR (ofs-ofs0)). omega.
                  (*eapply Mem.perm_max.*) apply M. rewrite Zplus_minus. omega.
      elim (NWR 0). omega.
                  (*eapply Mem.perm_max.*) apply M. omega.
  split; intros. eapply Mem.perm_storebytes_1; eassumption. eapply Mem.perm_storebytes_2; eassumption.
Qed.

Lemma store_forward: forall m b ofs v ch m'
      (M:Mem.store ch m b ofs v = Some m'),
      mem_forward m m'.
Proof. intros.
  apply Mem.store_storebytes in M.
  eapply storebytes_forward; eassumption.
Qed.

Lemma store_readonly: forall m b ofs v ch m'
      (M:Mem.store ch m b ofs v = Some m'),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof. intros.
  apply Mem.store_storebytes in M.
  eapply storebytes_readonly; eassumption.
Qed.




(*
Lemma store_forward: forall m b ofs v ch m'
      (M:Mem.store ch m b ofs v = Some m'),
      mem_forward m m'.
Proof. intros.
  split; intros.
    eapply Mem.store_valid_block_1; eassumption.
  split; intros.
    eapply Mem.perm_store_2; eassumption.
  red; intros.
    eapply Mem.load_store_other; try eassumption.
    destruct (eq_block b0 b); subst. 2: left; trivial.
    elim (H0 ofs).
    eapply Mem.perm_max.
    eapply Mem.store_valid_access_3; try eassumption.
    specialize (size_chunk_pos ch); intros; omega.
Qed.

Lemma storebytes_forward: forall m b ofs bytes m'
      (M: Mem.storebytes m b ofs bytes = Some m'),
      mem_forward m m'.
Proof. intros.
  split; intros.
    eapply Mem.storebytes_valid_block_1; eassumption.
  split; intros.
    eapply Mem.perm_storebytes_2; eassumption.
  red; intros.
  destruct bytes.
    eapply storebytes_nil; eassumption.
  eapply Mem.load_storebytes_other; try eassumption.
    destruct (eq_block b0 b); subst. 2: left; trivial.
    apply Mem.storebytes_range_perm in M.
    elim (H0 ofs). eapply Mem.perm_max. eapply M. simpl; xomega.
Qed.
*)

Lemma alloc_forward:
      forall m lo hi m' b
      (A: Mem.alloc m lo hi = (m',b)),
      mem_forward m m'.
Proof. intros.
split; intros.
  eapply Mem.valid_block_alloc; eassumption.
  eapply Mem.perm_alloc_4; try eassumption.
  intros N; subst. eapply (Mem.fresh_block_alloc _ _ _ _ _ A H).
Qed.

(*
Lemma unchanged_on_sym P m m' b:
  Mem.unchanged_on P m m' -> Mem.valid_block m b ->
  Mem.unchanged_on (fun bb z => P bb z /\ bb=b) m' m.
Proof. intros.
  destruct H as [U1 U2].
  split; intros; try (destruct H; subst b0).
      split; intros; eapply U1; trivial.
    rewrite U2; trivial. eapply U1; trivial.
Qed.
*)

Lemma loadbytes_unchanged_on (P : block -> Z -> Prop) m m' b ofs n:
  Mem.unchanged_on P m m' -> Mem.valid_block m b ->
  (forall i : Z, ofs <= i < ofs + n -> P b i) ->
  Mem.loadbytes m b ofs n = Mem.loadbytes m' b ofs n.
Proof. intros.
  symmetry. eapply Mem.loadbytes_unchanged_on_1; eauto.
Qed.

Lemma loadbytes_alloc_unchanged m1 lo hi m2 b :
  Mem.alloc m1 lo hi = (m2, b) ->
  forall n (b' : block) (ofs : Z),
  Mem.valid_block m1 b' ->
  Mem.loadbytes m2 b' ofs n = Mem.loadbytes m1 b' ofs n.
Proof. intros. symmetry.
  eapply loadbytes_unchanged_on; try eassumption.
  eapply (Mem.alloc_unchanged_on (fun bb z => True)). eassumption.
  simpl. trivial.
Qed.

Lemma alloc_readonly:
      forall m lo hi m' b
      (A: Mem.alloc m lo hi = (m',b)),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof. red; intros.
  split. eapply loadbytes_alloc_unchanged; try eassumption.
  intros; split. eapply Mem.perm_alloc_1; eassumption.
     intros. eapply Mem.perm_alloc_4; try eassumption.
     apply Mem.fresh_block_alloc in A.
     destruct (eq_block b0 b); trivial. subst. elim (A H).
Qed.

Lemma alloc_readonlyLD:
      forall m lo hi m' b
      (A: Mem.alloc m lo hi = (m',b)),
      forall b, Mem.valid_block m b -> readonlyLD m b m'.
Proof. red; intros.
  split. eapply Mem.load_alloc_unchanged; try eassumption.
  intros; split. eapply Mem.perm_alloc_1; eassumption.
     intros. eapply Mem.perm_alloc_4; try eassumption.
     apply Mem.fresh_block_alloc in A.
     destruct (eq_block b0 b); trivial. subst. elim (A H).
Qed.
(*
Lemma free_forward: forall b z0 z m m'
      (M: Mem.free m b z0 z = Some m'),
      mem_forward m m'.
Proof. intros.
split; intros.
  eapply Mem.valid_block_free_1; eassumption.
split; intros.
  eapply Mem.perm_free_3; eassumption.
red; intros. eapply Mem.load_free; try eassumption.
  destruct (zlt z0 z).
    left; intros N; subst.
    eapply (H0 z0).
    eapply Mem.perm_max.
    eapply Mem.perm_implies.
      eapply Mem.free_range_perm; try eassumption.
      omega.
    constructor.
  right; left; trivial.
Qed.
*)
Lemma free_forward: forall b z0 z m m'
      (M: Mem.free m b z0 z = Some m'),
      mem_forward m m'.
Proof. intros.
split; intros.
  eapply Mem.valid_block_free_1; eassumption.
  eapply Mem.perm_free_3; eassumption.
Qed.

Lemma loadbytes_free m1 bf lo hi m2:
  Mem.free m1 bf lo hi = Some m2 ->
  forall n (b : block) (ofs : Z),
  b <> bf \/ lo >= hi \/ ofs + n <= lo \/ hi <= ofs ->
  Mem.loadbytes m2 b ofs n = Mem.loadbytes m1 b ofs n.
Proof. intros.
  remember (Mem.loadbytes m2 b ofs n) as d; symmetry in Heqd.
  destruct d.
  { apply loadbytes_D in Heqd; destruct Heqd.
    rewrite (Mem.free_result _ _ _ _ _ H) in H2. simpl in H2.
    assert (F: Mem.range_perm m1 b ofs (ofs + n) Cur Readable).
      red; intros. eapply Mem.perm_free_3. eassumption.
        eapply H1. assumption.
    apply Mem.range_perm_loadbytes in F. destruct F as [bytes F]; rewrite F.
    apply loadbytes_D in F. destruct F. rewrite <- H2 in H4. subst; trivial.
  }
  { remember (Mem.loadbytes m1 b ofs n) as q; symmetry in Heqq.
    destruct q; trivial.
    apply loadbytes_D in Heqq. destruct Heqq as [F C].
    assert (Mem.range_perm m2 b ofs (ofs + n) Cur Readable).
    { red; intros. eapply Mem.perm_free_1. eassumption.
        destruct H0. left; trivial. right. omega.
      apply F. trivial.
    }
    apply Mem.range_perm_loadbytes in H1. rewrite Heqd in H1. destruct H1; discriminate.
  }
Qed.

Lemma free_readonlyLD: forall b lo hi m m'
      (M: Mem.free m b lo hi = Some m'),
      forall b, Mem.valid_block m b -> readonlyLD m b m'.
Proof. red; intros.
split.
  eapply Mem.load_free; try eassumption.
  destruct (eq_block b0 b); try subst b0. 2: left; trivial.
  right; destruct (zle hi lo). left; omega. right.
  destruct (zle (ofs + size_chunk chunk) lo). left; trivial. right.
  destruct (zle hi ofs); trivial. exfalso.
  destruct (zle ofs lo).
    eapply (NWR lo); clear NWR. omega.
    (*eapply Mem.perm_max.*)
    eapply Mem.perm_implies.
      eapply Mem.free_range_perm; try eassumption. omega. constructor.
  eapply (NWR ofs); clear NWR. specialize (size_chunk_pos chunk). intros; omega.
    (*eapply Mem.perm_max.*)
    eapply Mem.perm_implies.
      eapply Mem.free_range_perm; try eassumption. omega. constructor.
intros. specialize (Mem.free_range_perm _ _ _ _ _ M); intros F. red in F.
    split; intros. eapply Mem.perm_free_1; try eassumption.
      destruct (eq_block b0 b); try subst b0. 2: left; trivial. right.
      destruct (zlt ofs' lo). left; trivial. right. destruct (zle hi ofs'). trivial.
      elim (NWR _ H0). (* specialize (size_chunk_pos chunk). intros; omega.*)
      (*eapply Mem.perm_max.*) eapply Mem.perm_implies. apply F. omega. constructor.
    eapply Mem.perm_free_3; try eassumption.
Qed.

Lemma free_readonly: forall b lo hi m m'
      (M: Mem.free m b lo hi = Some m'),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof. red; intros.
destruct (zle n 0).
  split. repeat rewrite Mem.loadbytes_empty; trivial.
         intros; omega.
split.
  eapply loadbytes_free; try eassumption.
  destruct (eq_block b0 b); try subst b0. 2: left; trivial.
  right; destruct (zle hi lo). left; omega. right.
  destruct (zle (ofs + n) lo). left; trivial. right.
  destruct (zle hi ofs); trivial. exfalso.
  destruct (zle lo ofs).
    eapply (NWR 0); clear NWR. omega.
    (*eapply Mem.perm_max.*)
    eapply Mem.perm_implies.
      eapply Mem.free_range_perm; try eassumption. omega. constructor.
  eapply (NWR (lo - ofs)); clear NWR. omega. rewrite Zplus_minus.
    (*eapply Mem.perm_max.*)
    eapply Mem.perm_implies.
      eapply Mem.free_range_perm; try eassumption. omega. constructor.
intros. specialize (Mem.free_range_perm _ _ _ _ _ M); intros F. red in F.
    split; intros. eapply Mem.perm_free_1; try eassumption.
      destruct (eq_block b0 b); try subst b0. 2: left; trivial. right.
      destruct (zlt (ofs + i) lo). left; trivial. right. destruct (zle hi (ofs+i)). trivial.
      elim (NWR _ H0). (* specialize (size_chunk_pos chunk). intros; omega.*)
      (*eapply Mem.perm_max.*) eapply Mem.perm_implies. apply F. omega. constructor.
    eapply Mem.perm_free_3; try eassumption.
Qed.

Lemma freelist_forward: forall l m m'
      (M: Mem.free_list m l = Some m'),
      mem_forward m m'.
Proof. intros l.
  induction l; simpl; intros.
    inv M. apply mem_forward_refl.
  destruct a. destruct p.
  remember (Mem.free m b z0 z) as d.
  destruct d; inv M; apply eq_sym in Heqd.
  specialize (IHl _ _ H0).
  apply free_forward in Heqd.
  eapply mem_forward_trans; eassumption.
Qed.

Lemma freelist_readonly: forall l m m'
      (M: Mem.free_list m l = Some m'),
      forall b, Mem.valid_block m b -> readonly m b m'.
Proof.
  induction l; simpl; intros.
    inv M. apply readonly_refl.
  destruct a. destruct p.
  remember (Mem.free m b0 z0 z) as d.
  destruct d; inv M; apply eq_sym in Heqd.
  specialize (IHl _ _ H1).
  eapply readonly_trans.
    eapply (free_readonly _ _ _ _ _ Heqd _ H).
  eapply IHl. eapply free_forward; eassumption.
Qed.

Lemma freelist_readonlyLD: forall l m m'
      (M: Mem.free_list m l = Some m'),
      forall b, Mem.valid_block m b -> readonlyLD m b m'.
Proof.
  induction l; simpl; intros.
    inv M. apply readonlyLD_refl.
  destruct a. destruct p.
  remember (Mem.free m b0 z0 z) as d.
  destruct d; inv M; apply eq_sym in Heqd.
  specialize (IHl _ _ H1).
  eapply readonlyLD_trans.
    eapply (free_readonlyLD _ _ _ _ _ Heqd _ H).
  eapply IHl. eapply free_forward; eassumption.
Qed.

Lemma forward_nextblock: forall m m',
  mem_forward m m' ->
  (Mem.nextblock m <= Mem.nextblock m')%positive.
Proof.
intros m m' H1.
unfold mem_forward in H1.
unfold Mem.valid_block in H1.
apply Pos.leb_le.
remember (Pos.leb (Mem.nextblock m) (Mem.nextblock m')).
destruct b; trivial.
assert (H2: (Mem.nextblock m' < Mem.nextblock m)%positive).
  apply Pos.leb_gt. rewrite Heqb. trivial.
destruct (H1 (Mem.nextblock m')); auto.
xomega.
Qed.

Lemma inject_separated_incr_fwd:
  forall j j' m1 m2 j'' m2'
    (InjSep : inject_separated j j' m1 m2)
    (InjSep' : inject_separated j' j'' m1 m2')
    (InjIncr' : inject_incr j' j'')
    (Fwd: mem_forward m2 m2'),
    inject_separated j j'' m1 m2.
Proof.
intros. intros b. intros. remember (j' b) as z.
destruct z; apply eq_sym in Heqz.
destruct p. specialize (InjIncr' _ _ _ Heqz).
rewrite InjIncr' in H0. inv H0.
apply (InjSep _ _ _ H Heqz).
destruct (InjSep' _ _ _ Heqz H0).
split. trivial.
intros N. apply H2. eapply Fwd. apply N.
Qed.

Lemma inject_separated_incr_fwd2:
  forall j0 j j' m10 m20 m1 m2,
  inject_incr j j' ->
  inject_separated j j' m1 m2 ->
  inject_incr j0 j ->
  mem_forward m10 m1 ->
  inject_separated j0 j m10 m20 ->
  mem_forward m20 m2 ->
  inject_separated j0 j' m10 m20.
Proof.
intros until m2; intros H1 H2 H3 H4 H5 H6.
apply (@inject_separated_incr_fwd j0 j m10 m20 j' m2); auto.
unfold inject_separated.
intros b1 b2 delta H7 H8.
unfold inject_separated in H2, H5.
specialize (H2 b1 b2 delta H7 H8).
destruct H2 as [H21 H22].
unfold mem_forward in H4, H6.
specialize (H4 b1).
specialize (H6 b2).
split; intros CONTRA.
solve[destruct (H4 CONTRA); auto].
apply H22; auto.
Qed.

Lemma forall_inject_val_list_inject:
  forall j args args' (H:Forall2 (val_inject j) args args' ),
    Val.inject_list j args args'.
Proof.
intros j args.
induction args; intros;  inv H; constructor; eauto.
Qed.

Lemma val_list_inject_forall_inject:
  forall j args args' (H:Val.inject_list j args args'),
    Forall2 (val_inject j) args args' .
Proof.
intros j args.
induction args; intros;  inv H; constructor; eauto.
Qed.

Lemma forall_lessdef_val_listless:
  forall args args' (H: Forall2 Val.lessdef args args'),
    Val.lessdef_list args args' .
Proof.
intros args.
induction args; intros;  inv H; constructor; eauto.
Qed.

Lemma val_listless_forall_lessdef:
  forall args args' (H:Val.lessdef_list args args'),
    Forall2 Val.lessdef args args' .
Proof.
intros args.
induction args; intros;  inv H; constructor; eauto.
Qed.

Lemma storev_valid_block_1:
forall ch m addr v m',
Mem.storev ch m addr v = Some m' ->
(forall b, Mem.valid_block m b -> Mem.valid_block m' b).
Proof. intros. destruct addr; inv H. eapply Mem.store_valid_block_1; eauto. Qed.

Lemma storev_valid_block_2:
forall ch m addr v m',
Mem.storev ch m addr v = Some m' ->
(forall b, Mem.valid_block m' b -> Mem.valid_block m b).
Proof. intros. destruct addr; inv H. eapply Mem.store_valid_block_2; eauto. Qed.

(*This is an [F,V]-independent definition of meminj_preserves_globals*)
Definition meminj_preserves_globals_ind (globals: (block->Prop)*(block->Prop)) f :=
  (forall b, fst globals b -> f b = Some (b, 0)) /\
  (forall b, snd globals b -> f b = Some (b, 0)) /\
  (forall b1 b2 delta, snd globals b2 -> f b1 = Some (b2, delta) -> b1=b2).

Definition genv2blocks {F V: Type} (ge: Genv.t F V) :=
  (fun b => exists id, Genv.find_symbol ge id = Some b,
   fun b => exists gv, Genv.find_var_info ge b = Some gv).

Lemma meminj_preserves_genv2blocks:
  forall {F V: Type} (ge: Genv.t F V) j,
  meminj_preserves_globals_ind (genv2blocks ge) j <->
  Events.meminj_preserves_globals ge j.
Proof.
intros ge; split; intro H1.
unfold meminj_preserves_globals in H1.
unfold Events.meminj_preserves_globals.
destruct H1 as [H1 [H2 H3]].
split.
intros.
apply H1; auto.
unfold genv2blocks.
unfold Genv.find_symbol in H.
simpl; exists id; auto.
split.
intros b gv H4.
apply H2; auto.
unfold genv2blocks.
unfold Genv.find_var_info in H4.
simpl; exists gv; auto.
intros until gv; intros H4 H5.
symmetry.
eapply H3; eauto.
unfold genv2blocks.
unfold Genv.find_var_info in H4.
simpl; exists gv; auto.
unfold meminj_preserves_globals.
destruct H1 as [H1 [H2 H3]].
split.
intros b H4.
unfold genv2blocks in H4.
destruct H4; eapply H1; eauto.
split.
intros b H4.
destruct H4; eapply H2; eauto.
intros b1 b2 delta H4 H5.
unfold genv2blocks in H4.
destruct H4.
eapply H3 in H; eauto.
Qed.

Definition genvs_domain_eq {F1 F2 V1 V2: Type}
  (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) :=
    (forall b, fst (genv2blocks ge1) b <-> fst (genv2blocks ge2) b) /\
    (forall b, snd (genv2blocks ge1) b <-> snd (genv2blocks ge2) b) /\
    (forall b, (exists f, Genv.find_funct_ptr ge1 b = Some f)
           <-> (exists f, Genv.find_funct_ptr ge2 b = Some f)).

Lemma genvs_domain_eq_preserves:
  forall {F1 F2 V1 V2: Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) j,
  genvs_domain_eq ge1 ge2 ->
  (meminj_preserves_globals_ind (genv2blocks ge1) j <->
   meminj_preserves_globals_ind (genv2blocks ge2) j).
Proof.
intros until j; intros H1.
unfold meminj_preserves_globals.
destruct H1 as [DE1 DE2].
split; intros [H2 [H3 H4]].
split.
intros b H5.
cut (fst (genv2blocks ge1) b).
 intros H6.
apply (H2 b H6).
apply (DE1 b); auto.
split.
intros b H5.
apply H3; eauto.
apply DE2; auto.
intros b1 b2 delta H5 H6.
eapply H4; eauto.
apply DE2; auto.
split.
intros b H5.
eapply H2; eauto.
apply DE1; auto.
split.
intros b H5.
apply H3; auto.
apply DE2; auto.
intros until delta; intros H5 H6.
eapply H4; eauto.
apply DE2; auto.
Qed.

Lemma genvs_domain_eq_sym:
  forall {F1 F2 V1 V2: Type} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2),
  genvs_domain_eq ge1 ge2 -> genvs_domain_eq ge2 ge1.
Proof.
intros until ge2.
unfold genvs_domain_eq; intros [H1 H2].
split. intros b. split; intro H3; solve[destruct (H1 b); auto].
split. intros b. split; intro H3.
  destruct H2; eapply H; eauto.
  destruct H2; eapply H; eauto.
intros b. split.
  intros [ef F]. destruct H2 as [H2 H3]. rewrite H3; eauto.
  intros [ef F]. destruct H2 as [H2 H3]. rewrite <-H3; eauto.
Qed.

Lemma genvs_domain_eq_refl:
  forall F V (ge: Genv.t F V), genvs_domain_eq ge ge.
Proof.
intros F V ge; unfold genvs_domain_eq; split; try solve[intro b; split; auto].
split. intro b; split; auto.
intros b; split; auto.
Qed.

Lemma genvs_domain_eq_trans: forall {F1 F2 F3 V1 V2 V3: Type}
  (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2) (ge3: Genv.t F3 V3),
  genvs_domain_eq ge1 ge2 -> genvs_domain_eq ge2 ge3 -> genvs_domain_eq ge1 ge3.
Proof. intros F1 F2 F3 V1 V2 V3 ge1 ge2 ge3; unfold genvs_domain_eq.
  intros. destruct H; destruct H0.
  split. intros b. rewrite H. apply H0.
  split. intros b. destruct H1 as [H1 _]. rewrite H1.
    destruct H2 as [H2 _]. apply H2.
  intros b. destruct H2 as [H2 H3]. destruct H1 as [H1 H4].
    rewrite <-H3. rewrite H4. split; auto.
Qed.

Lemma genvs_domain_eq_match_genvs: forall {F1 V1 F2 V2:Type}
  (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2),
  genvs_domain_eq ge1 ge2 -> genv2blocks ge1 = genv2blocks ge2.
Proof. intros F1 V1 F2 V2 ge1 ge2.
  unfold genvs_domain_eq, genv2blocks. simpl; intros.
  destruct H.
  f_equal; extensionality b.
(*We use Axiom prop_ext here, but Lemma genvs_domain_eq_match_genvsB
in effect_simulations.v shows the same result of this lemma for Bool
rather than Prop*)
    apply prop_ext. apply H.
    apply prop_ext. apply H0.
Qed.

Lemma meminj_preserves_globals_ind_compose:
   forall {F1 V1 F2 V2} (ge1: Genv.t F1 V1) (ge2: Genv.t F2 V2)
   j1 j2 (G: genvs_domain_eq ge1 ge2)
   (PG1: meminj_preserves_globals_ind (genv2blocks ge1) j1)
   (PG2: meminj_preserves_globals_ind (genv2blocks ge2) j2),
   meminj_preserves_globals_ind (genv2blocks ge1) (compose_meminj j1 j2).
Proof. intros.
  destruct PG1 as [A12 [B12 C12]].
  destruct PG2 as [A23 [B23 C23]].
  split; intros.
     unfold compose_meminj. rewrite (A12 _ H).
     rewrite (A23 b). reflexivity.
     apply G. apply H.
  split; intros. unfold compose_meminj.
     rewrite (B12 _ H).
     rewrite (B23 b). reflexivity.
     apply G. apply H.
  rename b2 into b3.
    destruct (compose_meminjD_Some _ _ _ _ _ H0)
      as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear H0.
    assert (snd (genv2blocks ge2) b3). apply G; eassumption.
    specialize (C23 _ _ _ H0 J2). subst.
    specialize (C12 _ _ _ H J1). subst. trivial.
Qed.

Lemma meminj_preserves_incr_sep:
  forall {F V:Type} ge j (PG: @meminj_preserves_globals F V ge j)
         m tm (MINJ : Mem.inject j m tm)
         j' (INCR : inject_incr j j') (SEP: inject_separated j j' m tm),
  meminj_preserves_globals ge j'.
Proof. intros.
     apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in PG.
     destruct PG as [AA [BB CC]].
     split; intros. apply INCR. apply (AA _ H).
     split; intros. apply INCR. apply (BB _ H).
     remember (j b1) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p. rewrite (INCR _ _ _ Heqd) in H0. inv H0.
       apply (CC _ _ _ H Heqd).
     destruct (SEP _ _ _ Heqd H0).
       specialize (BB _ H).
       exfalso. apply H2; clear - BB MINJ.
       eapply Mem.valid_block_inject_2; try eassumption.
Qed.

Lemma meminj_preserves_incr_sep_vb:
  forall {F V:Type} ge j (PG: @meminj_preserves_globals F V ge j)
         m tm
         (VB: forall b1 b2 ofs, j b1 = Some(b2,ofs) ->
               (Mem.valid_block m b1 /\ Mem.valid_block tm b2))
         j' (INCR : inject_incr j j') (SEP: inject_separated j j' m tm),
  meminj_preserves_globals ge j'.
Proof. intros.
     apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in PG.
     destruct PG as [AA [BB CC]].
     split; intros. apply INCR. apply (AA _ H).
     split; intros. apply INCR. apply (BB _ H).
     remember (j b1) as d.
     destruct d; apply eq_sym in Heqd.
       destruct p. rewrite (INCR _ _ _ Heqd) in H0. inv H0.
       apply (CC _ _ _ H Heqd).
     destruct (SEP _ _ _ Heqd H0).
       specialize (BB _ H).
       destruct (VB _ _ _ BB). contradiction.
Qed.

Lemma mem_forward_nextblock:
  forall m m', mem_forward m m' -> Ple  (Mem.nextblock m) (Mem.nextblock m').
Proof.
intros. hnf in H.
unfold Mem.valid_block in H.
pose proof (Ppred_Plt (Mem.nextblock m)).
unfold Ple, Plt in *.
destruct (peq (Mem.nextblock m) 1).
rewrite e. apply Pos.le_1_l.
specialize (H0 n).
destruct (H _ H0) as [? _]; clear H.
pose proof (Pos.succ_pred _ n).
rewrite <- H; apply Pos.le_succ_l; auto.
Qed.

Lemma forward_unchanged_on: forall m m' (FWD: mem_forward m m')
           b ofs (NP: ~ Mem.perm m b ofs Max Nonempty),
     Mem.unchanged_on (fun b' ofs' => b' = b /\ ofs' = ofs) m m'.
Proof. intros.
split; intros.
  apply mem_forward_nextblock; auto.
  destruct H; subst.
  split; intros; elim NP.
    eapply Mem.perm_max.
    eapply Mem.perm_implies; try eassumption. apply perm_any_N.
    destruct (FWD _ H0) as [VB' P]. eapply Mem.perm_implies.
       apply P. eapply Mem.perm_max; eassumption. apply perm_any_N.
destruct H; subst.
  elim NP. eapply Mem.perm_max.
  eapply Mem.perm_implies; try eassumption. apply perm_any_N.
Qed.

Lemma unchanged_on_union:
      forall m m' P Q (HP: Mem.unchanged_on P m m') (HQ: Mem.unchanged_on Q m m')
             (PQ: block -> Z -> Prop) (HPQ: forall b ofs, PQ b ofs -> P b ofs \/ Q b ofs),
      Mem.unchanged_on PQ m m'.
Proof. intros.
  split; intros.
    apply HP.
    destruct (HPQ _ _ H).
      eapply HP; eassumption.
      eapply HQ; eassumption.
    destruct (HPQ _ _ H).
      eapply HP; eassumption.
      eapply HQ; eassumption.
Qed.

Lemma unchanged_on_validblock: forall m m' (U V: Values.block -> Z -> Prop)
   (UV: forall b ofs, Mem.valid_block m b -> (U b ofs -> V b ofs)),
   Mem.unchanged_on V m m' -> Mem.unchanged_on U m m'.
  Proof. intros.
    destruct H.
    split; intros. auto.
       eapply unchanged_on_perm; try eassumption. eauto.
       eapply unchanged_on_contents; try eassumption.
       apply Mem.perm_valid_block in H0. eauto.
Qed.

Lemma unchanged_on_validblock_invariant: forall m m' U V
   (UV: forall b ofs, Mem.valid_block m b -> (U b ofs <-> V b ofs)),
   Mem.unchanged_on V m m' <-> Mem.unchanged_on U m m'.
  Proof. intros.
    split; intros.
       eapply unchanged_on_validblock; try eassumption.
          intros. destruct (UV _ ofs H0). eauto.
       eapply unchanged_on_validblock; try eassumption.
          intros. destruct (UV _ ofs H0). eauto.
Qed.

Lemma unchanged_on_perm_intersection: forall m m' U (Fwd: mem_forward m m'),
   Mem.unchanged_on U m m' <->
   Mem.unchanged_on (fun b z => U b z /\ Mem.perm m b z Max Nonempty)  m m'.
  Proof. intros.
    split; intros Hyp.
    split; intros; eapply Hyp; eauto. apply H. apply H.
    split; intros.
   apply Hyp.
    remember (Mem.perm_dec m b ofs Max Nonempty).
      destruct s; clear Heqs.
         eapply Hyp; eauto.
      split; intros. exfalso. apply n; clear Hyp n.
         eapply Mem.perm_implies. eapply Mem.perm_max; eassumption.
               apply perm_any_N.
        exfalso. apply n; clear Hyp n.
        destruct (Fwd _ H0) as [VB' P]. apply P.
           eapply Mem.perm_implies. eapply Mem.perm_max; eassumption.
               apply perm_any_N.
     eapply Hyp; trivial.
       split; trivial.
        eapply Mem.perm_implies. eapply Mem.perm_max; eassumption.
               apply perm_any_N.
Qed.

Lemma unchanged_on_trans: forall m1 m2 m3 U
      (U1: Mem.unchanged_on U m1 m2)
      (U2: Mem.unchanged_on U m2 m3)
      (Fwd12: mem_forward m1 m2),
  Mem.unchanged_on U m1 m3.
Proof. intros.
split; intros.
   eapply Ple_trans; [apply U1 | apply U2].
  split; intros.
    eapply U2; trivial. apply Fwd12; trivial.
    eapply U1; trivial.
  eapply U1; trivial. eapply U2; trivial. apply Fwd12; trivial.
destruct U1 as [_ P1 V1]; destruct U2 as [_ P2 V2].
  rewrite (V2 _ _ H).
    apply V1; trivial.
  apply P1; trivial. eapply Mem.perm_valid_block; eassumption.
Qed.

(* Does not hold, since readonly refers to Cur permissions
Lemma ec_readonly_strong: forall
  (ef : external_function) (F V : Type) (ge : Genv.t F V)
    (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem)
    (EC: external_call ef ge vargs m1 t vres m2)
    b (VB: Mem.valid_block m1 b), readonly m1 b m2.
Proof. intros.
destruct ef; simpl in *; try inv EC; try apply readonly_refl.
(*functions are now by name*)
(*functions are now by name*)
{ inv H. apply readonly_refl. eapply store_readonly; eassumption. }
{ eapply readonly_trans. eapply alloc_readonly; eassumption.
  eapply store_readonly; try eassumption. eapply alloc_forward; eassumption. }
{ eapply free_readonly; eassumption. }
{ eapply storebytes_readonly; eassumption. }
{ apply (ec_readonly (inline_assembly_properties text sg)) in EC.
  (*destruct EC.*) red; intros; split; intros. Locate readonly.
  symmetry. eapply loadbytes_unchanged_on; try eassumption.
     intros. red. intros N. eapply (NWR (i-ofs)). omega.
     assert (ofs + (i - ofs) = i) by omega. rewrite H0.   Mem.perm_implies. eapply NWR.

 inv H0. apply readonly_refl. eapply store_readonly; eassumption. }
{ eapply readonly_trans. eapply alloc_readonly; eassumption.
  eapply store_readonly; try eassumption. eapply alloc_forward; eassumption. }
{ eapply free_readonly; eassumption. }
{ eapply storebytes_readonly; eassumption. }
Qed.
*)

Lemma external_call_mem_forward:
  forall (ef : external_function) (F V : Type) (ge : Genv.t F V)
    (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem),
    external_call ef ge vargs m1 t vres m2 -> mem_forward m1 m2.
Proof.
intros. intros b Hb.
split; intros. eapply external_call_valid_block; eauto.
eapply external_call_max_perm; eauto.
Qed.

(* Does not hold, since readonlyLD refers to Cur permissions
Lemma external_call_readonlyLD:
  forall (ef : external_function) (F V : Type) (ge : Genv.t F V)
    (vargs : list val) (m1 : mem) (t : trace) (vres : val) (m2 : mem),
    external_call ef ge vargs m1 t vres m2 ->
  forall b, Mem.valid_block m1 b -> readonlyLD m1 b m2.
Proof. intros.
  eapply readonly_readonlyLD.
  eapply ec_readonly_strong; eassumption.
Qed.
*)
Definition val_has_type_opt' (v: option val) (ty: typ) :=
 match v with
 | None => True
 | Some v' => Val.has_type v' ty
 end.

Definition val_has_type_opt (v: option val) (sig: signature) :=
  val_has_type_opt' v (proj_sig_res sig).

Definition is_vundef (v : val) : bool :=
  match v with
    | Vundef => true
    | _ => false
  end.

Definition vals_def (vs : list val) :=
  List.forallb (fun v => negb (is_vundef v)) vs.

Definition genv2blocksBool {F V : Type} (ge : Genv.t F V):=
  (fun b =>
      match Genv.invert_symbol ge b with
        Some id => true
      | None => false
      end,
   fun b => match Genv.find_var_info ge b with
                  Some gv => true
                | None => false
            end).

Definition isGlobalBlock {F V : Type} (ge : Genv.t F V) :=
  fun b => (fst (genv2blocksBool ge)) b || (snd (genv2blocksBool ge)) b.

Lemma invert_symbol_isGlobal: forall {V F} (ge : Genv.t F V) b x,
      Genv.invert_symbol ge b = Some x -> isGlobalBlock ge b = true.
Proof. intros.
  unfold isGlobalBlock, genv2blocksBool. simpl.
  rewrite H; simpl; trivial.
Qed.

Lemma find_symbol_isGlobal: forall {V F} (ge : Genv.t F V) x b
       (Find: Genv.find_symbol ge x = Some b), isGlobalBlock ge b = true.
Proof. intros.
  eapply invert_symbol_isGlobal.
  rewrite (Genv.find_invert_symbol _ _ Find). reflexivity.
Qed.

Lemma symbol_address_isGLobalBlock {V F} (ge : Genv.t F V) i1 i2 b i3:
  Genv.symbol_address ge i1 i2 = Vptr b i3 -> isGlobalBlock ge b=true.
Proof.
unfold Genv.symbol_address.
remember (Genv.find_symbol ge i1) as q.
destruct q; symmetry in Heqq; intros HH; inv HH.
apply find_symbol_isGlobal in Heqq; trivial.
Qed.

Lemma find_var_info_isGlobal: forall {V F} (ge : Genv.t F V) b x,
      Genv.find_var_info ge b = Some x -> isGlobalBlock ge b = true.
Proof. intros.
  unfold isGlobalBlock, genv2blocksBool. simpl.
  rewrite H, orb_true_r; trivial.
Qed.

Definition ReadOnlyBlocks {F V} (ge: Genv.t F V) (b:block): bool :=
  match Genv.find_var_info ge b with
          None => false
        | Some gv => gvar_readonly gv && negb (gvar_volatile gv)
  end.

Lemma ReadOnlyBlocks_global {F V} (g:Genv.t F V) b:
      ReadOnlyBlocks g b = true -> isGlobalBlock g b = true.
Proof.
   unfold ReadOnlyBlocks; intros.
   remember (Genv.find_var_info g b) as d. destruct d; try discriminate.
   eapply find_var_info_isGlobal. rewrite <- Heqd; reflexivity.
Qed.

Definition RDOnly_fwd (m1 m1':mem) B :=
  forall b (Hb: B b = true), readonly m1 b m1'.

Lemma RDOnly_fwd_trans m1 m2 m3 B:
  RDOnly_fwd m1 m2 B -> RDOnly_fwd m2 m3 B -> RDOnly_fwd m1 m3 B.
Proof. intros; red; intros.
  eapply readonly_trans. apply H; eauto. apply H0; eauto.
Qed.

Definition mem_respects_readonly {F V} (ge : Genv.t F V) m :=
    forall b gv, Genv.find_var_info ge b = Some gv ->
                 gvar_readonly gv && negb (gvar_volatile gv) = true ->
           Genv.load_store_init_data ge m b 0 (gvar_init gv) /\
           Mem.valid_block m b /\ (forall ofs : Z, ~ Mem.perm m b ofs Max Writable).

Lemma mem_respects_readonly_fwd {F V} (g : Genv.t F V) m m'
         (MRR: mem_respects_readonly g m)
         (FWD: mem_forward m m')
         (RDO: forall b, Mem.valid_block m b -> readonly m b m'):
         mem_respects_readonly g m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' Perm].
split. eapply Genv.load_store_init_data_invariant; try eassumption.
       intros. eapply readonly_readonlyLD. eapply RDO; try eassumption.
       intros. intros N. apply (NP ofs'). eapply Mem.perm_max; eassumption. (* apply NP.*)
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

Lemma mem_respects_readonly_forward {F V} (ge : Genv.t F V) m m'
         (MRR: mem_respects_readonly ge m)
         (FWD: mem_forward m m')
         (RDO: forall b gv, Genv.find_var_info ge b = Some gv ->
                 gvar_readonly gv && negb (gvar_volatile gv) = true -> readonly m b m'):
         mem_respects_readonly ge m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' Perm].
split. eapply Genv.load_store_init_data_invariant; try eassumption.
       intros. eapply readonly_readonlyLD. eapply RDO; try eassumption.
       intros. intros N. apply (NP ofs'). eapply Mem.perm_max; eassumption. (* apply NP.*)
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

Lemma mem_respects_readonly_forward' {F V} (ge : Genv.t F V) m m'
         (MRR: mem_respects_readonly ge m)
         (FWD: mem_forward m m')
         (RDO: RDOnly_fwd m m' (ReadOnlyBlocks ge)):
         mem_respects_readonly ge m'.
Proof. red; intros. destruct (MRR _ _ H H0) as [LSI [VB NP]]; clear MRR.
destruct (FWD _ VB) as [VB' Perm].
split. eapply Genv.load_store_init_data_invariant; try eassumption.
       intros. eapply readonly_readonlyLD. eapply RDO; try eassumption. unfold ReadOnlyBlocks. rewrite H; trivial.
       intros. intros N. apply (NP ofs'). eapply Mem.perm_max; eassumption. (* apply NP.*)
split. trivial.
intros z N. apply (NP z); eauto.
Qed.

(*The following 2 lemmas are from Cminorgenproof.v*)
Lemma nextblock_storev:
  forall chunk m addr v m',
  Mem.storev chunk m addr v = Some m' -> Mem.nextblock m' = Mem.nextblock m.
Proof.
  unfold Mem.storev; intros. destruct addr; try discriminate.
  eapply Mem.nextblock_store; eauto.
Qed.
Lemma nextblock_freelist:
  forall fbl m m',
  Mem.free_list m fbl = Some m' ->
  Mem.nextblock m' = Mem.nextblock m.
Proof.
  induction fbl; intros until m'; simpl.
  congruence.
  destruct a as [[b lo] hi].
  case_eq (Mem.free m b lo hi); intros; try congruence.
  transitivity (Mem.nextblock m0). eauto. eapply Mem.nextblock_free; eauto.
Qed.
Lemma perm_freelist:
  forall fbl m m' b ofs k p,
  Mem.free_list m fbl = Some m' ->
  Mem.perm m' b ofs k p ->
  Mem.perm m b ofs k p.
Proof.
  induction fbl; simpl; intros until p.
  congruence.
  destruct a as [[b' lo] hi]. case_eq (Mem.free m b' lo hi); try congruence.
  intros. eauto with mem.
Qed.


Lemma get_freelist:
  forall fbl m m' (FL: Mem.free_list m fbl = Some m') b
  (H: forall b' lo hi, In (b', lo, hi) fbl -> b' <> b) z,
  ZMap.get z (Mem.mem_contents m') !! b =
  ZMap.get z (Mem.mem_contents m) !! b.
Proof. intros fbl.
  induction fbl; simpl; intros; inv FL; trivial.
  destruct a. destruct p.
  remember (Mem.free m b0 z1 z0) as d.
  destruct d; inv H1. apply eq_sym in Heqd.
  rewrite (IHfbl _ _ H2 b).
     clear IHfbl H2.
     case_eq (eq_block b0 b); intros.
      exfalso. eapply (H b0). left. reflexivity. assumption.
     apply Mem.free_result in Heqd. subst. reflexivity.
  eauto.
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


Section ALLOC.

Variable m1: mem.
Variables lo hi: Z.
Variable m2: mem.
Variable b: Values.block.
Hypothesis ALLOC: Mem.alloc m1 lo hi = (m2, b).

Transparent Mem.alloc.
Lemma AllocContentsUndef:
     (Mem.mem_contents m2) !! b = ZMap.init Undef.
Proof.
   injection ALLOC. simpl; intros. subst.
   simpl. rewrite PMap.gss. reflexivity.
Qed.
Lemma AllocContentsOther: forall b', b' <> b ->
     (Mem.mem_contents m2) !! b' = (Mem.mem_contents m1) !! b'.
Proof.
   injection ALLOC. simpl; intros. subst. simpl.
   rewrite PMap.gso; trivial.
Qed.
Opaque Mem.alloc.

Lemma AllocContentsUndef1: forall z,
     ZMap.get z (Mem.mem_contents m2) !! b = Undef.
Proof. intros. rewrite AllocContentsUndef . apply ZMap.gi. Qed.

Lemma AllocContentsOther1: forall b', b' <> b ->
      (Mem.mem_contents m2) !! b' = (Mem.mem_contents m1) !! b'.
Proof. intros. rewrite AllocContentsOther; trivial. Qed.

Lemma alloc_contents:
 forall b1 ofs,
    Mem.valid_block m1 b1 ->
  ZMap.get ofs (PMap.get b1 (Mem.mem_contents m1)) =
  ZMap.get ofs (PMap.get b1 (Mem.mem_contents m2)).
Proof.
 intros.
Transparent Mem.alloc. unfold Mem.alloc in ALLOC. Opaque Mem.alloc.
inv ALLOC. simpl.
unfold Mem.valid_block in H.
rewrite PMap.gso; auto.
intro; subst. apply Plt_strict in H; auto.
Qed.


End ALLOC.

Definition gvar_info_eq {V1 V2} (v1: option (globvar V1)) (v2: option (globvar V2)) :=
  match v1, v2 with
    None, None => True
  | Some i1, Some i2 => gvar_init i1 = gvar_init i2 /\
                        gvar_readonly i1 = gvar_readonly i2 /\ gvar_volatile i1 = gvar_volatile i2
  | _, _ => False
  end.

Definition gvar_infos_eq {F1 V1 F2 V2}
  (g1 : Genv.t F1 V1) (g2 : Genv.t F2 V2) :=
  forall b, gvar_info_eq (Genv.find_var_info g1 b) (Genv.find_var_info g2 b).

Lemma gvar_info_refl V v: @gvar_info_eq V V v v.
  destruct v; simpl; intuition. Qed.

Lemma gvar_infos_eqD {F1 V1 F2 V2} (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
         (G: gvar_infos_eq ge1 ge2) b v1 (Hb: Genv.find_var_info ge1 b = Some v1):
      exists v2, Genv.find_var_info ge2 b = Some v2 /\ gvar_init v1 = gvar_init v2 /\
                 gvar_readonly v1 = gvar_readonly v2 /\ gvar_volatile v1 = gvar_volatile v2.
Proof. specialize (G b); rewrite Hb in G. red in G.
  destruct (Genv.find_var_info ge2 b); try contradiction.
  exists g. intuition.
Qed.

Lemma gvar_infos_eqD2 {F1 V1 F2 V2} (ge1 : Genv.t F1 V1) (ge2 : Genv.t F2 V2)
         (G: gvar_infos_eq ge1 ge2) b v2 (Hb: Genv.find_var_info ge2 b = Some v2):
      exists v1, Genv.find_var_info ge1 b = Some v1 /\ gvar_init v1 = gvar_init v2 /\
                 gvar_readonly v1 = gvar_readonly v2 /\ gvar_volatile v1 = gvar_volatile v2.
Proof. specialize (G b); rewrite Hb in G. red in G.
  destruct (Genv.find_var_info ge1 b); try contradiction.
  exists g. intuition.
Qed.

Lemma gvar_infos_eq_ReadOnlyBlocks {F1 V1 F2 V2} (g1: Genv.t F1 V1) (g2:Genv.t F2 V2):
      gvar_infos_eq g1 g2 -> ReadOnlyBlocks g1 = ReadOnlyBlocks g2.
Proof. intros.
  unfold ReadOnlyBlocks. extensionality b.
  remember (Genv.find_var_info g1 b) as d1.
  destruct d1; symmetry in Heqd1.
    apply (gvar_infos_eqD _ _ H) in Heqd1. destruct Heqd1 as [gv2 [? [? [? ?]]]].
       rewrite H0, H2, H3. trivial.
  remember (Genv.find_var_info g2 b) as q.
  destruct q; symmetry in Heqq.
    apply (gvar_infos_eqD2 _ _ H) in Heqq. destruct Heqq as [gv1 [? [? [? ?]]]].
    rewrite H0 in Heqd1. discriminate.
  trivial.
Qed.

(*****************The following variant is used in the linker***********)
Definition gvars_included {V1 V2} (gv1:option (globvar V1)) (gv2: option (globvar V2)): Prop :=
  match gv1, gv2 with
   None, None => True
 | None, Some x2 => True
 | Some x1, None => False
 | Some x1, Some x2 => gvar_init x1 = gvar_init x2 /\
                       gvar_readonly x1 = gvar_readonly x2 /\
                       gvar_volatile x1 = gvar_volatile x2
 end.

Lemma gvars_cohereD {F1 V1 F2 V2} (ge1:Genv.t F1 V1) (ge2:Genv.t F2 V2)
    (HG: forall b, gvars_included (Genv.find_var_info ge1 b)
                   (Genv.find_var_info ge2 b))
    b gv1 (GV: Genv.find_var_info ge1 b = Some gv1):
     exists gv2, Genv.find_var_info ge2 b = Some gv2 /\
                 gvar_init gv1 = gvar_init gv2 /\
                 gvar_readonly gv1 = gvar_readonly gv2 /\
                 gvar_volatile gv1 = gvar_volatile gv2.
Proof.
 specialize (HG b); rewrite GV in HG. simpl in HG.
 destruct (Genv.find_var_info ge2 b); try contradiction.
 exists g; eauto.
Qed.

(****************************************************************************)

Definition findsymbols_preserved {F1 V1 F2 V2}
           (g1 : Genv.t F1 V1) (g2 : Genv.t F2 V2) :=
  forall i b, Genv.find_symbol g1 i = Some b -> Genv.find_symbol g2 i = Some b.
