Require Import compcert.lib.Axioms.
Require Import compcert.lib.Maps.

Require Import VST.concurrency.common.sepcomp.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.


Require Import Coq.ZArith.ZArith.

Require Import VST.concurrency.common.permissions.
Require Import compcert.common.Memory. (*for Mem.perm_order'' *)
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.common.permissions.

Require Import VST.sepcomp.semantics_lemmas.
Require Import compcert.lib.Coqlib.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.

Require Import Coq.Logic.FunctionalExtensionality.

Lemma CLight_Deterministic: forall ge c m c1 m1 c2 m2,
    veric.Clight_new.cl_step ge c m c2 m2 ->
    veric.Clight_new.cl_step ge c m c1 m1 ->
    c1 = c2 /\ m1 = m2.
Proof. intros.
       specialize (cl_corestep_fun _ _ _ _ _ _ _ H H0); intros X; inversion X; subst. split; trivial.
Qed.

Definition bnd_from_init m := bounded_maps.bounded_map (snd (getMaxPerm m)) /\ (Mem.mem_access m).1 = fun z k => None.

Lemma mem_storebytes_counded_init:
  forall m m' b ofs bytes,
    bnd_from_init m ->
    Mem.storebytes m b ofs bytes = Some m' ->
    bnd_from_init m'.
Proof.
  intros ? ? ? ? ? H0 H.
  destruct H0; split.
  unfold getMaxPerm in *. erewrite Mem.storebytes_access; eauto.
  erewrite Mem.storebytes_access; eauto.
Qed.

Lemma mem_alloc_bounded_init:
  forall m lo hi m1 b,
    bnd_from_init m ->
    Mem.alloc m lo hi = (m1, b) ->
    bnd_from_init m1.
Proof.
  { intros ? ? ? ? ? H0 H.
    Transparent Mem.alloc. unfold Mem.alloc in H. Opaque Mem.alloc.
    inversion H; clear H; subst.
    destruct H0; split; simpl in *; trivial.
    red; intros. red in H.
    rewrite (PTree.gmap1 (fun f : Z -> perm_kind -> option permission => f^~ Max)
                         p (PTree.set (Mem.nextblock m)
                                      (fun (ofs : Z) (_ : perm_kind) => if zle lo ofs && zlt ofs hi then Some Freeable else None)
                                      (Mem.mem_access m).2)) in H1.
    unfold option_map in H1.
    rewrite PTree.gsspec in H1.
    destruct (peq p (Mem.nextblock m)); subst.
    { inversion H1; clear H1; subst. clear H0 H. red.
      exists hi, lo; split; intros.
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; omega. }
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; omega. } }
    { apply (H p); clear H0. rewrite PTree.gmap1. apply H1. } }
Qed.


Lemma mem_free_bounded_init:
  forall m lo hi m' b,
    bnd_from_init m ->
    Mem.free m b lo hi = Some m' ->
    bnd_from_init m'.
Proof.
  intros ? ? ? ? ? H0 Heqq.
  Transparent Mem.free. unfold Mem.free in Heqq. Opaque Mem.free.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); try discriminate.
  inversion Heqq; clear Heqq; subst.
  destruct H0 as [? INI]; split.
  intros p f F.  simpl.
  destruct (peq p b); subst.
  { simpl in F. rewrite PTree.gmap1 in F. unfold option_map in F. rewrite PTree.gss in F. inversion F; clear F; subst.
    specialize (H b).
    remember (((getMaxPerm m).2) ! b) as g. destruct g; symmetry in Heqg.
    { assert (Some o = Some o) by trivial. specialize (H _ H0); clear H0. rename o into g.
      destruct H as [HI [LO [HHi HLo]]]. unfold getMaxPerm in Heqg. unfold PMap.get. simpl in *.
      rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg. rewrite INI.
      destruct (((Mem.mem_access m).2) ! b); try discriminate. inversion Heqg; clear Heqg; subst.
      exists  HI, LO; split; intros.
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; eauto. }
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; eauto. } }
    { clear H. unfold getMaxPerm in Heqg.
      destruct (zlt lo hi).
      { assert (A: lo <= lo < hi) by omega. specialize (r _ A).
        apply Mem.perm_max in r. unfold Mem.perm, PMap.get in r.
        rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg.
        remember (((Mem.mem_access m).2) ! b) as q. destruct q; simpl in *. discriminate.
        rewrite INI in r. inversion r. }
      { simpl in Heqg. rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg. unfold PMap.get.
        remember (((Mem.mem_access m).2) ! b) as w. destruct w; try discriminate. clear Heqg.
        rewrite INI.
        exists lo, lo; split; intros.
        { destruct (zle lo p); destruct (zlt p hi); simpl; trivial. }
        { destruct (zle lo p); destruct (zlt p hi); simpl; trivial. } } } }
  { apply (H p). unfold getMaxPerm in *; simpl in *.
    rewrite PTree.gmap1 in F. rewrite PTree.gmap1. unfold option_map in *.
    rewrite PTree.gso in F; trivial. }
  simpl; trivial.
Qed.

Lemma mem_drop_perm_bounded_init:
  forall m b lo hi P m',
    bnd_from_init m ->
    Mem.drop_perm m b lo hi P = Some m' ->
    bnd_from_init m'.
Proof.
  intros ? ? ? ? ? ? H0 Heqq.
  Transparent Mem.drop_perm. unfold Mem.drop_perm in Heqq. Opaque Mem.drop_perm.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); try discriminate.
  inversion Heqq; clear Heqq; subst.
  destruct H0 as [? INI]; split.
  - intros p f F.  simpl.
    destruct (peq p b); subst.
    { simpl in F.
      rewrite PTree.gmap1 in F.
      unfold option_map in F.
      rewrite PTree.gss in F.
      inversion F; clear F; subst.
      specialize (H b).
      remember (((getMaxPerm m).2) ! b) as g. destruct g; symmetry in Heqg.
      { assert (Some o = Some o) by trivial. specialize (H _ H0); clear H0. rename o into g.
      destruct H as [HI [LO [HHi HLo]]]. unfold getMaxPerm in Heqg. unfold PMap.get. simpl in *.
      rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg. rewrite INI.
      destruct (((Mem.mem_access m).2) ! b); try discriminate. inversion Heqg; clear Heqg; subst.
      exists  (Z.max HI hi), (Z.min LO lo); split; intros.
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; eauto.
        - move : H=> /Z.gt_lt_iff /Z.max_lub_lt_iff [] ? ?.
          xomega.
        - move : H=> /Z.gt_lt_iff /Z.max_lub_lt_iff [] /Z.gt_lt_iff /HHi //.
        - move : H=> /Z.gt_lt_iff /Z.max_lub_lt_iff [] /Z.gt_lt_iff /HHi //.
        - move : H=> /Z.gt_lt_iff /Z.max_lub_lt_iff [] /Z.gt_lt_iff /HHi //.
      }
      { destruct (zle lo p); destruct (zlt p hi); simpl; trivial; eauto.
        - move : H=> /Z.min_glb_lt_iff [] ? ?.
          xomega.
        - move : H=> /Z.min_glb_lt_iff [] ? ?.
          omega.
        - move : H=> /Z.min_glb_lt_iff [] /HLo //.
        - move : H=> /Z.min_glb_lt_iff [] /HLo //.
      } }
    { clear H. unfold getMaxPerm in Heqg.
      destruct (zlt lo hi).
      { assert (A: lo <= lo < hi) by omega. specialize (r _ A).
        apply Mem.perm_max in r. unfold Mem.perm, PMap.get in r.
        rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg.
        remember (((Mem.mem_access m).2) ! b) as q. destruct q; simpl in *. discriminate.
        rewrite INI in r. inversion r. }
      { simpl in Heqg. rewrite PTree.gmap1 in Heqg. unfold option_map in Heqg. unfold PMap.get.
        remember (((Mem.mem_access m).2) ! b) as w. destruct w; try discriminate. clear Heqg.
        rewrite INI.
        exists lo, lo; split; intros.
        { destruct (zle lo p); destruct (zlt p hi); simpl; trivial. xomega. }
        { destruct (zle lo p); destruct (zlt p hi); simpl; trivial. xomega.  } } } }
  { apply (H p). unfold getMaxPerm in *; simpl in *.
    rewrite PTree.gmap1 in F. rewrite PTree.gmap1. unfold option_map in *.
    rewrite PTree.gso in F; trivial. }
  simpl; trivial.
Qed.

Lemma mem_free_list_bounded_init:
  forall m l m',
    bnd_from_init m ->
    Mem.free_list m l = Some m' ->
    bnd_from_init m'.
Proof.
  intros ? ? ? H0 H.
  { generalize dependent m'. generalize dependent m. induction l; intros.
    { inversion H; clear H; subst. trivial. }
    { destruct a as [[b lo] hi]. simpl in H. remember (Mem.free m b lo hi) as q; symmetry in Heqq.
      destruct q; try discriminate. apply (IHl m0); trivial. clear H IHl m'.
      rename m0 into m'.
      eapply mem_free_bounded_init; eauto.
  } }
Qed.

Lemma preserve_bnd: memstep_preserve (fun m m' => bnd_from_init m -> bnd_from_init m').
Proof.
  econstructor; intros; eauto.
  induction H; intros.
  - eapply mem_storebytes_counded_init; eauto.
  - eapply mem_alloc_bounded_init; eauto.
  - eapply mem_free_list_bounded_init; eauto.
  - eauto.
Qed.

Lemma CLight_step_mem_bound' ge c m c' m':
  veric.Clight_new.cl_step ge c m c' m' -> bnd_from_init m -> bnd_from_init m'.
Proof.
  intros.
  apply (memsem_preserves (CLN_memsem ge) _ preserve_bnd _ _ _ _ H H0).
Qed.

(*This proof is already in juicy_machine.
 * move it to a more general position.*)
Lemma Mem_canonical_useful: forall m loc k,
    fst (Mem.mem_access m) loc k = None.
Proof. intros. destruct m; simpl in *.
       unfold PMap.get in nextblock_noaccess.
       pose (b:= Pos.max (TreeMaxIndex (snd mem_access) + 1 )  nextblock).
       assert (H1:  ~ Plt b nextblock).
       { intros H. assert (HH:= Pos.le_max_r (TreeMaxIndex (snd mem_access) + 1) nextblock).
         clear - H HH. unfold Pos.le in HH. unfold Plt in H.
         apply HH. eapply Pos.compare_gt_iff.
         auto. }
       assert (H2 :( b > (TreeMaxIndex (snd mem_access)))%positive ).
       { assert (HH:= Pos.le_max_l (TreeMaxIndex (snd mem_access) + 1) nextblock).
         apply Pos.lt_gt. eapply Pos.lt_le_trans; eauto.
         xomega. }
       specialize (nextblock_noaccess b loc k H1).
       apply max_works in H2. rewrite H2 in nextblock_noaccess.
       assumption.
Qed.

Lemma mem_bound_init_mem_bound:
  forall m,
    bounded_maps.bounded_map (snd (getMaxPerm m)) <->
    bnd_from_init m.
Proof.
  repeat (split; intros) ; eauto.
  - extensionality x;
    extensionality y;
    eapply Mem_canonical_useful.
  - destruct H; auto.
Qed.

Lemma CLight_step_mem_bound ge c m c' m':
  veric.Clight_new.cl_step ge c m c' m' ->
  bounded_maps.bounded_map (snd (getMaxPerm m)) ->
  bounded_maps.bounded_map (snd (getMaxPerm m')).
Proof.
  intros.
  eapply CLight_step_mem_bound' in H;
  apply mem_bound_init_mem_bound; eauto.
Qed.


Definition bounded_mem (m: mem) := bounded_maps.bounded_map (snd (getMaxPerm m)) .


Lemma mem_alloc_bounded:
  forall m lo hi m1 b,
    bounded_mem m ->
    Mem.alloc m lo hi = (m1, b) ->
    bounded_mem m1.
Proof.
  intros m lo hi m1 b H H0.
  apply mem_bound_init_mem_bound; eauto.
  eapply mem_alloc_bounded_init; eauto.
  apply mem_bound_init_mem_bound; eauto.
Qed.

Lemma drop_perm_bounded:
  forall m b lo hi P m',
    bounded_mem m ->
    Mem.drop_perm m b lo hi P = Some m' ->
    bounded_mem m'.
Proof.
  intros m b lo hi P m' H H0.
  apply mem_bound_init_mem_bound; eauto.
  eapply mem_drop_perm_bounded_init ; eauto.
  apply mem_bound_init_mem_bound; eauto.
Qed.

Lemma store_bounded:
  forall Mint32 m b ofs v m',
    bounded_mem m ->
    Mem.store Mint32 m b ofs v = Some m' ->
    bounded_mem m'.
Proof.
  intros Mint m b ofs v m' H H0.
  eapply mem_bound_init_mem_bound; eauto.
  eapply mem_storebytes_counded_init; eauto.
  - eapply mem_bound_init_mem_bound; eauto.
  - eapply Mem.store_storebytes; eauto.
Qed.

Lemma bounded_getMaxPerm:
  forall m p Hlt,
    @bounded_mem m ->
    @bounded_mem (@restrPermMap p m Hlt).
Proof.
  intros ? ? ? H b f.
  rewrite /restrPermMap /= PTree.gmap1 PTree.gmap.
  move: (H b f).
  rewrite /getMaxPerm /= PTree.gmap1.
  destruct (((Mem.mem_access m).2) ! b)=> //.
Qed.

Lemma store_init_data_bounded:
  forall F V ge m b ofs data m',
    bounded_mem m ->
    @Globalenvs.Genv.store_init_data F V ge m b ofs data = Some m' ->
    bounded_mem m'.
Proof.
  intros.
  move: H0.
  destruct data; simpl;
  try eapply store_bounded; eauto.
  - intros HH; inversion HH.
    subst; auto.
  - destruct ( Globalenvs.Genv.find_symbol ge i);
    try solve[intros HH; inversion HH];
    eapply store_bounded; eauto.
Qed.

Lemma store_init_data_list_bounded:
  forall F V ge m b ofs B m',
    bounded_mem m ->
    @Globalenvs.Genv.store_init_data_list F V ge m b ofs B = Some m' ->
    bounded_mem m'.
Proof.
  intros.
  move: m' ofs b m H H0.
  induction B.
  - intros; inversion H0; subst; auto.
  - intros; simpl in H0.
    destruct (Globalenvs.Genv.store_init_data ge m b ofs a) eqn:STORE_INIT;
      try solve[inversion H0].
    eapply IHB; try apply H0.
    eapply store_init_data_bounded; eauto.
Qed.

Lemma store_zeros_init_data_bounded:
  forall m b ofs a m',
    bounded_mem m ->
    Globalenvs.store_zeros m b ofs a = Some m' ->
    bounded_mem m'.
Proof.
  intros.
  destruct (zle a 0) eqn:AA.
  - rewrite Globalenvs.store_zeros_equation in H0.
    rewrite AA in H0; inversion H0; subst; auto.
  - assert (exists n, Z.of_nat n = a).
    { exists (nat_of_Z a).
      apply nat_of_Z_eq. omega. }
    destruct H1 as [n H1].
    subst a.
    clear g AA.
    move: n m b ofs m' H H0.
    induction n.
    + intros.
      rewrite Globalenvs.store_zeros_equation in H0.
      rewrite Nat2Z.inj_0 in H0.
      destruct (zle 0 0); try omega.
      inversion H0; subst; assumption.
    + intros.
      rewrite Globalenvs.store_zeros_equation in H0.
      destruct (zle (Z.of_nat n.+1) 0).
      { rewrite Nat2Z.inj_succ in l.
        assert (HH:=coqlib4.Z_of_nat_ge_O n).
        clear - l HH.
        xomega.
      }
      destruct ( Mem.store AST.Mint8unsigned m b ofs Values.Vzero) eqn:STORE';
        try solve[inversion H0].
      replace (Z.of_nat n.+1 - 1) with (Z.of_nat n) in H0 by xomega.
      eapply IHn; try eapply H0.
      eapply store_bounded; eauto.
Qed.

Lemma alloc_global_bounded:
  forall F V ge m m' a,
    @bounded_mem m ->
    @Globalenvs.Genv.alloc_global F V ge m a = Some m' ->
    @bounded_mem m'.
Proof.
  move => ? ? ge m m' [] ? a BND.
  rewrite /Globalenvs.Genv.alloc_global.
  destruct a.
  - destruct (Mem.alloc m 0 1) eqn:ALLOC; intros DROP;
    try solve[inversion DROP].
    eapply drop_perm_bounded; try eapply DROP.
    eapply mem_alloc_bounded; eauto.
  - remember (AST.init_data_list_size (AST.gvar_init v)) as  A; clear HeqA.
    destruct (Mem.alloc m 0 A) eqn:ALLOC.
    destruct (Globalenvs.store_zeros m0 b 0 ) eqn:STORE;
      try solve[intros HH; inversion HH ].
    remember ((AST.gvar_init v)) as  B; clear HeqB.
    destruct (Globalenvs.Genv.store_init_data_list ge m1 b 0 B) eqn:STORE_INIT;
      try solve[intros HH; inversion HH ].
    intros DROP.
    eapply drop_perm_bounded; try eapply DROP. clear DROP.
    eapply store_init_data_list_bounded;
      try eapply STORE_INIT.
    eapply store_zeros_init_data_bounded; try eapply STORE.
    eapply mem_alloc_bounded; eauto.
Qed.

