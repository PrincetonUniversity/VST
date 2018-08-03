Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import VST.msl.Extensionality.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.common.core_semantics.

Require Import VST.msl.Coqlib2.

(********************* Lemmas and definitions related to mem_step ********)

Lemma mem_step_refl m: mem_step m m.
  apply (mem_step_freelist _ _ nil); trivial.
Qed.

Lemma mem_step_free:
      forall m b lo hi m', Mem.free m b lo hi = Some m' -> mem_step m m'.
Proof.
 intros. eapply (mem_step_freelist _ _ ((b,lo,hi)::nil)).
 simpl. rewrite H; reflexivity.
Qed.

Lemma mem_step_store:
      forall m ch b a v m', Mem.store ch m b a v = Some m' -> mem_step m m'.
Proof.
 intros. eapply mem_step_storebytes. eapply Mem.store_storebytes; eassumption.
Qed.

Record memstep_preserve (P:mem -> mem -> Prop) :=
  {
    preserve_trans: forall m1 m2 m3, P m1 m2 -> P m2 m3 -> P m1 m3;
    preserve_mem: forall m m', mem_step m m' -> P m m'
  }.

Lemma preserve_refl {P} (HP: memstep_preserve P): forall m, P m m.
Proof. intros. eapply (preserve_mem _ HP). apply mem_step_refl. Qed.

Lemma preserve_free {P} (HP: memstep_preserve P):
      forall m b lo hi m', Mem.free m b lo hi = Some m' -> P m m'.
Proof.
 intros. eapply (preserve_mem _ HP). eapply mem_step_free; eauto. Qed.

Theorem preserve_conj {P Q} (HP:memstep_preserve P) (HQ: memstep_preserve Q):
        memstep_preserve (fun m m' => P m m' /\ Q m m').
Proof.
intros. constructor.
+ intros. destruct H; destruct H0. split. eapply HP; eauto. eapply HQ; eauto.
+ intros; split. apply HP; trivial. apply HQ; trivial.
Qed.

(*opposite direction appears not to hold*)
Theorem preserve_impl {A} (P:A -> mem -> mem -> Prop) (Q:A->Prop):
        (forall a, Q a -> memstep_preserve (P a)) -> memstep_preserve (fun m m' => forall a, Q a -> P a m m').
Proof.
intros.
constructor; intros.
+ eapply H; eauto.
+ apply H; eauto.
Qed.

Lemma preserve_exensional {P Q} (HP:memstep_preserve P) (PQ:P=Q): memstep_preserve Q.
subst; trivial. Qed.

(*opposite direction appears not to hold*)
Theorem preserve_univ {A} (P:A -> mem -> mem -> Prop):
        (forall a, memstep_preserve (P a)) -> memstep_preserve (fun m m' => forall a, P a m m').
Proof. intros.
eapply preserve_exensional.
eapply (@preserve_impl A (fun a m m'=> P a m m') (fun a=>True)).
intros. apply H. extensionality m. extensionality m'. apply prop_ext. intuition.
Qed.

Theorem mem_forward_preserve: memstep_preserve mem_forward.
Proof.
constructor.
+ apply mem_forward_trans.
+ intros. induction H.
  eapply storebytes_forward; eassumption.
  eapply alloc_forward; eassumption.
  eapply freelist_forward; eassumption.
  eapply mem_forward_trans; eassumption.
Qed.

Theorem readonly_preserve b: memstep_preserve (fun m m' => mem_forward m m' /\ (Mem.valid_block m b -> readonly m b m')).
Proof.
constructor.
+ intros. destruct H; destruct H0.
  split; intros. eapply mem_forward_trans; eassumption.
  eapply readonly_trans; eauto. apply H2. apply H. eassumption.
+ intros; induction H.
  - split; intros. eapply storebytes_forward; eassumption.
    eapply storebytes_readonly; eassumption.
  - intros.
    split; intros. eapply alloc_forward; eassumption.
    eapply alloc_readonly; eassumption.
  - intros.
    split; intros. eapply freelist_forward; eassumption.
    eapply freelist_readonly; eassumption.
  - destruct IHmem_step1; destruct IHmem_step2.
    split. eapply mem_forward_trans; eassumption.
    intros. eapply readonly_trans. eauto. apply H4. apply H1; eassumption.
Qed.

Theorem readonly_preserve':
   memstep_preserve (fun m m' => mem_forward m m' /\ (forall b, Mem.valid_block m b -> readonly m b m')).
Proof.
eapply preserve_exensional.
eapply preserve_univ; intros. apply (readonly_preserve a).
  extensionality m. extensionality m'. apply prop_ext.
  split; intros. split. eapply H. apply xH. intros. eapply (H b). trivial.
  destruct H. split; eauto.
Qed.

Lemma storebytes_unch_loc_unwritable b ofs: forall l m m' (L: Mem.storebytes m b ofs l = Some m'),
      Mem.unchanged_on (loc_not_writable m) m m'.
Proof.
intros.
split; intros.
+ rewrite (Mem.nextblock_storebytes _ _ _ _ _ L); apply Pos.le_refl.
+ split; intros.
  eapply Mem.perm_storebytes_1; eassumption.
  eapply Mem.perm_storebytes_2; eassumption.
+ rewrite (Mem.storebytes_mem_contents _ _ _ _ _ L).
  apply Mem.storebytes_range_perm in L.
  destruct (eq_block b0 b); subst.
  - destruct (zle ofs ofs0).
      destruct (zlt ofs0 (ofs + Z.of_nat (length l))).
        elim H. eapply Mem.perm_max. apply L. omega.
      rewrite PMap.gss. apply Mem.setN_other. intros. omega.
    rewrite PMap.gss. apply Mem.setN_other. intros. omega.
  - rewrite PMap.gso; trivial.
Qed.

Lemma unch_on_loc_not_writable_trans m1 m2 m3
        (Q : Mem.unchanged_on (loc_not_writable m1) m1 m2)
        (W : Mem.unchanged_on (loc_not_writable m2) m2 m3)
        (F:mem_forward m1 m2):
     Mem.unchanged_on (loc_not_writable m1) m1 m3.
Proof.
  destruct Q as [Q0 Q1 Q2]. destruct W as [W0 W1 W2].
  split; intros.
  - eapply Ple_trans; eassumption.
  - cut (Mem.perm m2 b ofs k p <-> Mem.perm m3 b ofs k p).
      specialize (Q1 _ _ k p H H0). intuition.
    apply W1; clear W1. intros N. apply H. apply Q1; trivial. apply F; trivial.
  -  rewrite W2; clear W2.
       apply Q2; trivial.
     intros N; apply H. apply F; trivial. eapply Mem.perm_valid_block; eassumption.
     apply Q1; trivial. eapply Mem.perm_valid_block; eassumption.
Qed.

Theorem loc_not_writable_preserve:
   memstep_preserve (fun m m' => mem_forward m m' /\ Mem.unchanged_on (loc_not_writable m) m m').
Proof.
constructor.
+ intros. destruct H as [F1 Q]; destruct H0 as [F2 W].
  split; intros. eapply mem_forward_trans; eassumption. clear F2.
  eapply unch_on_loc_not_writable_trans; eassumption.
+ intros; induction H.
  - split; intros. eapply storebytes_forward; eassumption.
    eapply storebytes_unch_loc_unwritable; eassumption.
  - split; intros. eapply alloc_forward; eassumption.
    eapply Mem.alloc_unchanged_on; eassumption.
  - split; intros. eapply freelist_forward; eassumption.
    generalize dependent m.
    induction l; simpl; intros. inv H. apply Mem.unchanged_on_refl.
    destruct a. destruct p.
    remember (Mem.free m b z0 z) as w. destruct w; inv H. symmetry in Heqw.
    eapply unch_on_loc_not_writable_trans.
      eapply Mem.free_unchanged_on. eassumption.
        intros i I N. elim N; clear N.
        eapply Mem.perm_max. eapply Mem.perm_implies. eapply Mem.free_range_perm; eassumption. constructor.
      apply IHl; eassumption.
      eapply free_forward; eassumption.
  - destruct IHmem_step1; destruct IHmem_step2.
    split. eapply mem_forward_trans; eassumption.
    intros. clear H H0 H3. eapply unch_on_loc_not_writable_trans; eassumption.
Qed.

Lemma freelist_perm: forall l m m' (L : Mem.free_list m l = Some m') b (B: Mem.valid_block m b)
      ofs (P': Mem.perm m' b ofs Max Nonempty) k p,
      Mem.perm m b ofs k p <-> Mem.perm m' b ofs k p.
Proof. induction l; simpl; intros.
+ inv L; split; trivial.
+ destruct a. destruct p0.
  remember (Mem.free m b0 z0 z) as w. symmetry in Heqw.
  destruct w; inv L.
  specialize (IHl _ _  H0 _ (Mem.valid_block_free_1 _ _ _ _ _ Heqw _ B) _ P' k p).
  assert (P: Mem.perm m b ofs k p <-> Mem.perm m0 b ofs k p).
  { clear IHl. destruct (Mem.perm_free_list _ _ _ _ _ _ _ H0 P') as [P ?]; clear H0 P'.
    destruct (eq_block b0 b); subst.
    - destruct (zlt ofs z0).
      * split; intros. apply (Mem.perm_free_1 _ _ _ _ _ Heqw) in H0; eauto.
        eapply Mem.perm_free_3; eassumption.
      * destruct (zle z ofs).
        split; intros. apply (Mem.perm_free_1 _ _ _ _ _ Heqw) in H0; eauto.
                       eapply Mem.perm_free_3; eassumption.
        split; intros.
          eelim (Mem.perm_free_2 _ _ _ _ _ Heqw ofs Max Nonempty); clear Heqw; trivial. omega.
        eelim (Mem.perm_free_2 _ _ _ _ _ Heqw ofs Max Nonempty); clear Heqw. omega.
          eapply Mem.perm_implies. eapply Mem.perm_max. eassumption. constructor.
    - split; intros.
      * eapply (Mem.perm_free_1 _ _ _ _ _ Heqw); trivial. intuition.
      * eapply (Mem.perm_free_3 _ _ _ _ _ Heqw); trivial.
  }
  intuition.
Qed.

Theorem perm_preserve:
   memstep_preserve (fun m m' =>  mem_forward m m' /\ forall b, Mem.valid_block m b -> forall ofs, Mem.perm m' b ofs Max Nonempty ->
                                  forall k p, Mem.perm m b ofs k p <-> Mem.perm m' b ofs k p).
Proof.
constructor.
+ intros; split. eapply mem_forward_trans. apply H. apply H0.
  destruct H; destruct H0. intros.
  assert (M: Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p).
  - clear H2. apply H1; trivial. apply H0; trivial. apply H; trivial.
  - clear H1.
    assert (VB2: Mem.valid_block m2 b). apply H; trivial.
    destruct (H2 _ VB2 _ H4 k p); destruct M. split; intros; eauto.
+ intros; induction H.
  - split; intros. eapply storebytes_forward; eassumption.
    split; intros. eapply Mem.perm_storebytes_1; eassumption.
    eapply Mem.perm_storebytes_2; eassumption.
  - split; intros. eapply alloc_forward; eassumption.
    split; intros. eapply Mem.perm_alloc_1; eassumption.
    eapply Mem.perm_alloc_4; try eassumption.
    intros N; subst b'. elim (Mem.fresh_block_alloc _ _ _ _ _ H H0).
  - intros; split. eapply freelist_forward; eassumption.
    apply (freelist_perm _ _ _ H).
  - clear H H0. destruct IHmem_step1; destruct IHmem_step2.
    split. eapply mem_forward_trans; eassumption.
    intros.
    assert (M: Mem.perm m b ofs k p <-> Mem.perm m'' b ofs k p).
    * clear H2. apply H0; trivial. apply H1; trivial. apply H; trivial.
    * clear H0.
      assert (VB2: Mem.valid_block m'' b). apply H; trivial.
      destruct (H2 _ VB2 _ H4 k p); destruct M. split; intros; eauto.
Qed.

Lemma mem_step_forward m m': mem_step m m' -> mem_forward m m'.
intros. apply preserve_mem; trivial.
eapply mem_forward_preserve; trivial.
Qed.

Lemma freelist_perm_inv: forall l m m' (L : Mem.free_list m l = Some m') b (B: Mem.valid_block m b)
      ofs k p (P: Mem.perm m b ofs k p),
      Mem.perm m b ofs Max Freeable \/ Mem.perm m' b ofs k p.
Proof. induction l; simpl; intros.
+ inv L. right; trivial.
+ destruct a. destruct p0.
  remember (Mem.free m b0 z0 z) as w. symmetry in Heqw.
  destruct w; inv L.
  exploit Mem.perm_free_inv; eauto. intros [[HHx HH] | HH]; try subst b0.
  - left. eapply Mem.perm_max.  eapply Mem.free_range_perm; eassumption.
  - destruct (IHl _ _  H0 _ (Mem.valid_block_free_1 _ _ _ _ _ Heqw _ B) _ _ _ HH); clear IHl.
    2: right; trivial.
    left. eapply Mem.perm_free_3; eauto.
Qed.

Theorem preserves_max_eq_or_free:
   memstep_preserve (fun m m' =>  mem_forward m m' /\
                                  forall b (VB: Mem.valid_block m b) ofs,
                                   (forall k p, Mem.perm m b ofs k p <-> Mem.perm m' b ofs k p) \/
                                   (Mem.perm m b ofs Max Freeable /\
                                    Mem.perm_order'' None ((Mem.mem_access m') !! b ofs Max))).
Proof.
constructor.
+ intros; split. eapply mem_forward_trans. apply H. apply H0.
  destruct H; destruct H0. intros.
  assert (VB2: Mem.valid_block m2 b). { apply H; trivial. }
  destruct (H1 _ VB ofs) as [K1 | [K1 L1]]; destruct (H2 _ VB2 ofs) as [K2 | [K2 L2]]; clear H1 H2.
  - left; intros. specialize (K1 k p); specialize (K2 k p). intuition.
  - right; split; trivial. apply K1; trivial.
  - right; split; trivial. simpl in *. specialize (K2 Max).
    unfold Mem.perm in *.
    remember ((Mem.mem_access m3) !! b ofs Max) as w; destruct w; trivial.
    destruct ((Mem.mem_access m2) !! b ofs Max); try contradiction.
    destruct (K2 p); simpl in *. apply H2. apply perm_refl.
  - right; split; trivial.
+ intros; induction H.
  - split; intros. eapply storebytes_forward; eassumption.
    left; intros. split; intros.
    * eapply Mem.perm_storebytes_1; eassumption.
    * eapply Mem.perm_storebytes_2; eassumption.
  - split; intros. eapply alloc_forward; eassumption.
    left; intros. split; intros.
    * eapply Mem.perm_alloc_1; eassumption.
    * eapply Mem.perm_alloc_4; try eassumption.
      intros N; subst. eapply Mem.fresh_block_alloc; eassumption.
  - split; intros. eapply freelist_forward; eassumption.
    destruct (Mem.perm_dec m' b ofs Max Nonempty).
    * left; intros. eapply freelist_perm; eassumption.
    * destruct (Mem.perm_dec m b ofs Max Freeable); trivial.
       right; split; trivial. unfold Mem.perm in n; simpl in *.
       destruct ((Mem.mem_access m') !! b ofs Max); trivial.
       elim n; clear n. constructor.
      left; intros.
      split; intros. 2: eapply perm_freelist; eassumption.
      exploit freelist_perm_inv; eauto. intros [X | X]; trivial; contradiction.
  - clear H H0. destruct IHmem_step1; destruct IHmem_step2.
    split. eapply mem_forward_trans; eassumption.
    intros.
    assert (VB2 : Mem.valid_block m'' b). { apply H; trivial. }
    specialize (H0 _ VB ofs). specialize (H2 _ VB2 ofs).
    destruct H0 as [K | [K1 K2]]; destruct H2 as [L | [L1 L2]].
    * left; intros. split; intros. apply L. apply K; trivial.
      apply K. apply L; trivial.
    * right. split; trivial. apply K; trivial.
    * right. split; trivial.
      clear K1. unfold Mem.perm in *. simpl in *. specialize (L Max).
      remember ((Mem.mem_access m') !! b ofs Max) as d; destruct d; trivial.
      destruct ((Mem.mem_access m'') !! b ofs Max); try contradiction.
      specialize (L p); simpl in *. apply L. apply perm_refl.
    * right. split; trivial.
Qed.

Theorem mem_step_max_eq_or_free m m' (STEP: mem_step m m') b (VB: Mem.valid_block m b) ofs:
       (forall k p, Mem.perm m b ofs k p <-> Mem.perm m' b ofs k p) \/
       (Mem.perm m b ofs Max Freeable /\ None = ((Mem.mem_access m') !! b ofs Max)).
Proof. intros.
exploit preserve_mem. apply preserves_max_eq_or_free. eassumption.
simpl; intros [A B]. destruct (B _ VB ofs). left; trivial. right.
  destruct H; split; trivial.
  destruct ((Mem.mem_access m') !! b ofs Max); trivial; contradiction.
Qed.

Lemma memsem_preserves {C} (s: @MemSem C) P (HP:memstep_preserve P):
      forall c m c' m', corestep s c m c' m'-> P m m'.
Proof. intros.
  apply corestep_mem in H.
  eapply preserve_mem; eassumption.
Qed.

Lemma corestep_fwd {C} (s:@MemSem C) c m c' m'
   (CS:corestep s c m c' m' ): mem_forward m m'.
Proof.
eapply memsem_preserves; try eassumption. apply mem_forward_preserve.
Qed.

Lemma corestep_rdonly {C} (s:@MemSem C) c m c' m'
   (CS:corestep s c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
eapply (memsem_preserves s _ readonly_preserve'); eassumption.
Qed.

Lemma mem_step_nextblock:  memstep_preserve (fun m m' => Mem.nextblock m <= Mem.nextblock m')%positive.
constructor.
+ intros. xomega.
+ induction 1.
 - apply Mem.nextblock_storebytes in H;
   rewrite H; xomega.
 - apply Mem.nextblock_alloc in H.
   rewrite H. clear. xomega.
 - apply nextblock_freelist in H.
   rewrite H; xomega.
 - xomega.
Qed.

Lemma mem_step_nextblock':
  forall m m',
     mem_step m m' ->
   (Mem.nextblock m <= Mem.nextblock m')%positive.
Proof. apply mem_step_nextblock. Qed.

(*E-step: Axiomatization of external steps - potentially useful when Memory interface is hardened
Inductive e_step m m' : Prop :=
    mem_step_estep: mem_step m m' -> e_step m m'
  | drop_perm_estep: forall b lo hi p,
      Mem.drop_perm m b lo hi p = Some m' -> e_step m m'
  | change_cur_estep:
      (forall b ofs, (Mem.mem_access m) !! b ofs Max = (Mem.mem_access m') !! b ofs Max) ->
      Mem.unchanged_on (loc_not_writable m) m m' ->
      (Mem.mem_contents m = Mem.mem_contents m') ->
      Mem.nextblock m = Mem.nextblock m' -> e_step m m'
  | estep_trans: forall m'',
       e_step m m'' -> e_step m'' m' -> e_step m m'.

Lemma e_step_refl m: e_step m m.
Proof. apply mem_step_estep. apply mem_step_refl. Qed.

Lemma estep_forward m m' (E:e_step m m'): mem_forward m m'.
Proof.
induction E.
apply mem_forward_preserve; eassumption.
+ split; intros.
    eapply Mem.drop_perm_valid_block_1; eassumption.
    eapply Mem.perm_drop_4; eassumption.
+ split; intros.
  unfold Mem.valid_block in *. rewrite H2 in *; assumption.
  unfold Mem.perm. rewrite H. apply H4.
+ eapply mem_forward_trans; eassumption.
Qed.

Lemma estep_unch_on_loc_not_writable m m' (E:e_step m m'): Mem.unchanged_on (loc_not_writable m) m m'.
Proof.
induction E.
+ apply loc_not_writable_preserve in H. apply H.
+ unfold Mem.drop_perm in H.
  destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inv H; simpl in *.
  split; simpl; trivial.
  intros. red in H.
  unfold Mem.perm; simpl. rewrite PMap.gsspec.
  destruct (peq b0 b); subst; simpl. 2: intuition.
  destruct (zle lo ofs); simpl. 2: intuition.
  destruct (zlt ofs hi); simpl. 2: intuition.
  elim H. eapply Mem.perm_max. eapply Mem.perm_implies. apply r. omega. constructor.
+ trivial.
+ eapply unch_on_loc_not_writable_trans; try eassumption. eapply estep_forward; eassumption.
Qed.
*)
(*
Theorem loadbytes_drop m b lo hi p m' (D:Mem.drop_perm m b lo hi p = Some m'):
  forall b' ofs,
  b' <> b \/ ofs < lo \/ hi <= ofs \/ perm_order p Readable ->
  Mem.loadbytes m' b' ofs 1 = Mem.loadbytes m b' ofs 1.
Proof.
  intros.
Transparent Mem.loadbytes.
  unfold Mem.loadbytes.
  destruct (Mem.range_perm_dec m b' ofs (ofs + 1) Cur Readable).
  rewrite pred_dec_true.
  unfold Mem.drop_perm in D. destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inv D. simpl. auto.
  red; intros. specialize (Mem.perm_drop_1 _ _ _ _ _ _ D ofs0 Cur); intros.
    destruct (eq_block b' b); subst.
      destruct H. eapply Mem.perm_drop_3. eassumption. left; trivial. apply r. trivial.
      destruct (zlt ofs lo). eapply Mem.perm_drop_3. eassumption. right. omega. apply r. trivial.
      destruct H. omega.
      destruct (zle hi ofs). eapply Mem.perm_drop_3. eassumption. right. omega. apply r. trivial.
      destruct H. omega.
      eapply Mem.perm_implies. apply H1. omega. trivial.
   eapply Mem.perm_drop_3. eassumption. left; trivial. apply r. omega.

  destruct (Mem.range_perm_dec m' b' ofs (ofs + 1) Cur Readable); trivial.
  elim n; clear n. red; intros. eapply Mem.perm_drop_4. eassumption. apply r. trivial.
Qed.
*)

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
* revert m ofs0 H H0 H1; induction bytes; intros.
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
 apply AllocContentsOther with (b':=b) in H1.
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
   eapply Mem.perm_implies. apply Heqo. omega. constructor.
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
   eapply Pos.lt_le_trans; eauto.
 }
 erewrite IHmem_step1 by auto. apply IHmem_step2; auto.
 contradict H0.
 clear - H H1_ H0.
 revert H H0; induction H1_; intros.
 eapply Mem.perm_storebytes_2; eauto.
 pose proof (Mem.perm_alloc_inv _ _ _ _ _ H _ _ _ _ H1).
 destruct (eq_block b b'); subst; trivial.
 - pose proof (Mem.alloc_result _ _ _ _ _ H).
   subst. apply Plt_strict in H0. contradiction.
 - eapply Mem.perm_free_list in H; try apply H1.
   destruct H; auto.
 - eapply IHH1_1; auto. eapply IHH1_2; eauto.
   apply mem_step_nextblock in H1_1.
   unfold Mem.valid_block in *.
   eapply Pos.lt_le_trans; eauto.
Qed.

Lemma ple_load m ch a v
            (LD: Mem.loadv ch m a = Some v)
            m1 (PLE: perm_lesseq m m1):
           Mem.loadv ch m1 a = Some v.
Proof.
unfold Mem.loadv in *.
destruct a; auto.
Transparent Mem.load.
unfold Mem.load in *.
Opaque Mem.load.
destruct PLE.
if_tac in LD; [ | inv LD].
rewrite if_true.
rewrite <- LD; clear LD.
f_equal. f_equal.
destruct H.
rewrite size_chunk_conv in H.
clear - H perm_le_cont.
forget (size_chunk_nat ch) as n.
forget (Ptrofs.unsigned i) as j.
revert j H; induction n; intros; simpl; f_equal.
apply perm_le_cont.
apply (H j).
rewrite inj_S.
omega.
apply IHn.
rewrite inj_S in H.
intros ofs ?; apply H. omega.
clear - H perm_le_Cur.
destruct H; split; auto.
intros ? ?. specialize (H ofs H1).
hnf in H|-*.
specialize (perm_le_Cur b ofs).
destruct ((Mem.mem_access m) !! b ofs Cur); try contradiction.
destruct ((Mem.mem_access m1) !! b ofs Cur);
inv perm_le_Cur; auto; try constructor; try inv H.
Qed.

Lemma ple_store:
  forall ch m v1 v2 m' m1
   (PLE: perm_lesseq m m1),
   Mem.storev ch m v1 v2 = Some m' ->
   exists m1', perm_lesseq m' m1' /\ Mem.storev ch m1 v1 v2 = Some m1'.
Proof.
intros.
unfold Mem.storev in *.
destruct v1; try discriminate.
Transparent Mem.store.
unfold Mem.store in *.
Opaque Mem.store.
destruct (Mem.valid_access_dec m ch b (Ptrofs.unsigned i)  Writable); inv H.
destruct (Mem.valid_access_dec m1 ch b (Ptrofs.unsigned i)
      Writable).
*
eexists; split; [ | reflexivity].
destruct PLE.
constructor; simpl; auto.
intros. unfold Mem.perm in H. simpl in H.
forget (Ptrofs.unsigned i) as z.
destruct (eq_block b0 b). subst.
rewrite !PMap.gss.
forget (encode_val ch v2) as vl.
assert (z <= ofs < z + Z.of_nat (length vl) \/ ~ (z <= ofs < z + Z.of_nat (length vl))) by omega.
destruct H0.
clear - H0.
forget ((Mem.mem_contents m1) !! b) as mA.
forget ((Mem.mem_contents m) !! b) as mB.
revert z mA mB H0; induction vl; intros; simpl.
simpl in H0; omega.
simpl length in H0; rewrite inj_S in H0.
destruct (zeq z ofs).
subst ofs.
rewrite !Mem.setN_outside by omega. rewrite !ZMap.gss; auto.
apply IHvl; omega.
rewrite !Mem.setN_outside by omega.
apply perm_le_cont. auto.
rewrite !PMap.gso by auto.
apply perm_le_cont. auto.
*
contradiction n; clear n.
destruct PLE.
unfold Mem.valid_access in *.
destruct v; split; auto.
hnf in H|-*; intros.
specialize (H _ H1).
clear - H perm_le_Cur.
specialize (perm_le_Cur b ofs).
hnf in H|-*.
destruct ((Mem.mem_access m) !! b ofs Cur); try contradiction.
inv H;
destruct ((Mem.mem_access m1) !! b ofs Cur);
inv perm_le_Cur; auto; try constructor; try inv H.
Qed.

Lemma free_access_inv m b lo hi m' (FR: Mem.free m b lo hi = Some m') b' ofs k p
  (P: (Mem.mem_access m') !! b' ofs k = Some p):  (Mem.mem_access m) !! b' ofs k = Some p.
Proof.
apply Mem.free_result in FR; subst. simpl in *.
rewrite PMap.gsspec in P.
destruct (peq b' b); subst; trivial.
destruct (zle lo ofs && zlt ofs hi); inv P; trivial.
Qed.

Lemma free_access_inv_None m b lo hi m' (FR: Mem.free m b lo hi = Some m') b' ofs k
  (P: (Mem.mem_access m') !! b' ofs k = None):
  (b' = b /\ Z.le lo ofs /\ Z.lt ofs hi /\  (Mem.mem_access m) !! b' ofs k = Some Freeable) \/
  ((b' <> b \/ Z.lt ofs lo \/ Z.le hi ofs) /\ (Mem.mem_access m) !! b' ofs k = None).
Proof.
specialize (Mem.free_result _ _ _ _ _ FR). intros; subst. simpl in *.
rewrite PMap.gsspec in P.
destruct (peq b' b); subst.
+ remember (zle lo ofs && zlt ofs hi) as q.
  destruct q; inv P.
  - left. split; trivial. destruct (zle lo ofs); simpl in *; try discriminate.
    split; trivial. destruct (zlt ofs hi); simpl in *; try discriminate.
    split; trivial.
    assert (RP: Mem.perm m b ofs Cur Freeable). apply (Mem.free_range_perm _ _ _ _ _ FR ofs); omega.
    destruct k.
    * eapply Mem.perm_max in RP.
      unfold Mem.perm in RP. destruct ((Mem.mem_access m) !! b ofs Max); simpl in *; try discriminate.
      destruct p; simpl in *; try inv RP; simpl; trivial. contradiction.
    * unfold Mem.perm in RP. destruct ((Mem.mem_access m) !! b ofs Cur); simpl in *; try discriminate.
      destruct p; simpl in *; try inv RP; simpl; trivial. contradiction.
  - right; split; trivial. right.
    destruct (zle lo ofs); destruct (zlt ofs hi); simpl in *; try discriminate; try omega.
+ right; split; trivial. left; trivial.
Qed.

Lemma ple_free: forall m m' b lo hi (FL: Mem.free m b lo hi = Some m') m1 (PLE:perm_lesseq m m1),
      exists m1', Mem.free m1 b lo hi = Some m1' /\ perm_lesseq m' m1'.
Proof. intros.
  specialize (Mem.free_range_perm _ _ _ _ _ FL). intros.
  assert (RF: Mem.range_perm m1 b lo hi Cur Freeable).
  { destruct PLE. red; intros.
    specialize (perm_le_Cur b ofs). specialize (H _ H0). unfold Mem.perm in *.
    destruct ((Mem.mem_access m) !! b ofs Cur); simpl in *; try contradiction.
    destruct ((Mem.mem_access m1) !! b ofs Cur); simpl in *; try contradiction.
    eapply perm_order_trans; eassumption.
  }
  destruct (Mem.range_perm_free m1 b lo hi RF) as [mm MM].
  exists mm; split; trivial.
  destruct PLE.
  split; intros.
  - specialize (perm_le_Cur b0 ofs); clear perm_le_Max perm_le_cont.
    remember ((Mem.mem_access mm) !! b0 ofs Cur) as q; symmetry in Heqq.
      destruct q; simpl in *.
      * rewrite (free_access_inv _ _ _ _ _ MM _ _ _ _ Heqq) in *.
        remember ((Mem.mem_access m') !! b0 ofs Cur) as w; symmetry in Heqw.
         destruct w; trivial.
         rewrite (free_access_inv _ _ _ _ _ FL _ _ _ _ Heqw) in *. simpl in *; trivial.
      * remember ((Mem.mem_access m') !! b0 ofs Cur) as w; symmetry in Heqw.
        destruct w; trivial.
        rewrite (free_access_inv _ _ _ _ _ FL _ _ _ _ Heqw) in *.
        destruct (free_access_inv_None _ _ _ _ _ MM _ _ _ Heqq).
        ++ destruct H0 as [? [? [? ?]]]; subst.
           rewrite (Mem.free_result _ _ _ _ _ FL) in *. simpl in *.
           rewrite PMap.gss in Heqw.
           remember (zle lo ofs&& zlt ofs hi ) as t; destruct t; simpl in *; try discriminate.
           destruct (zle lo ofs); destruct (zlt ofs hi); simpl in *; try discriminate; omega.
        ++ destruct H0 as [? ?]. rewrite H1 in *; simpl in *; contradiction.
  - specialize (perm_le_Max b0 ofs); clear perm_le_Cur perm_le_cont.
    remember ((Mem.mem_access mm) !! b0 ofs Max) as q; symmetry in Heqq.
      destruct q; simpl in *.
      * rewrite (free_access_inv _ _ _ _ _ MM _ _ _ _ Heqq) in *.
        remember ((Mem.mem_access m') !! b0 ofs Max) as w; symmetry in Heqw.
         destruct w; trivial.
         rewrite (free_access_inv _ _ _ _ _ FL _ _ _ _ Heqw) in *. simpl in *; trivial.
      * remember ((Mem.mem_access m') !! b0 ofs Max) as w; symmetry in Heqw.
        destruct w; trivial.
        rewrite (free_access_inv _ _ _ _ _ FL _ _ _ _ Heqw) in *.
        destruct (free_access_inv_None _ _ _ _ _ MM _ _ _ Heqq).
        ++ destruct H0 as [? [? [? ?]]]; subst.
           rewrite (Mem.free_result _ _ _ _ _ FL) in *. simpl in *.
           rewrite PMap.gss in Heqw.
           remember (zle lo ofs&& zlt ofs hi ) as t; destruct t; simpl in *; try discriminate.
           destruct (zle lo ofs); destruct (zlt ofs hi); simpl in *; try discriminate; omega.
        ++ destruct H0 as [? ?]. rewrite H1 in *; simpl in *; contradiction.
  - rewrite (Mem.free_result _ _ _ _ _ FL). rewrite (Mem.free_result _ _ _ _ _ MM).
    simpl. apply perm_le_cont. eapply Mem.perm_free_3; eassumption.
  - rewrite (Mem.free_result _ _ _ _ _ FL). rewrite (Mem.free_result _ _ _ _ _ MM).
    simpl; trivial.
Qed.

Lemma ple_freelist: forall l m m' (FL: Mem.free_list m l = Some m') m1 (PLE:perm_lesseq m m1),
      exists m1', Mem.free_list m1 l = Some m1' /\ perm_lesseq m' m1'.
Proof. induction l; simpl; intros.
+ inv FL;  exists m1; split; trivial.
+ destruct a as [[b lo] hi]. remember (Mem.free m b lo hi) as q. destruct q; inv FL.
  symmetry in Heqq.
  destruct (ple_free _ _ _ _ _ Heqq _ PLE) as [mm [MMF MM]]. rewrite MMF. eauto.
Qed.

Lemma ple_storebytes:
  forall m b ofs bytes m' m1
   (PLE: perm_lesseq m m1),
   Mem.storebytes m b ofs bytes = Some m' ->
   exists m1', perm_lesseq m' m1' /\ Mem.storebytes m1 b ofs bytes = Some m1'.
Proof.
intros. Transparent Mem.storebytes. unfold Mem.storebytes in *. Opaque Mem.storebytes.
remember (Mem.range_perm_dec m b ofs (ofs + Z.of_nat (length bytes)) Cur Writable ) as d.
destruct d; inv H.
destruct (Mem.range_perm_dec m1 b ofs (ofs + Z.of_nat (length bytes)) Cur Writable).
+ clear Heqd.
  eexists; split. 2: reflexivity.
  destruct PLE.
  split; intros; simpl.
  - simpl. apply perm_le_Cur.
  - simpl. apply perm_le_Max.
  - simpl in *. rewrite PMap.gsspec. rewrite PMap.gsspec.
    destruct (peq b0 b); subst.
    * destruct (zlt ofs0 ofs).
      ++ rewrite Mem.setN_outside. 2: left; trivial.  rewrite Mem.setN_outside. 2: left; trivial.  apply perm_le_cont. apply H.
      ++ destruct (zle (ofs+Z.of_nat (length bytes)) ofs0).
         rewrite Mem.setN_outside. 2: right; xomega.  rewrite Mem.setN_outside. 2: right; xomega.  apply perm_le_cont. apply H.
         clear - g g0.
         remember ((Mem.mem_contents m1) !! b) as mA. clear HeqmA.
         remember ((Mem.mem_contents m) !! b) as mB. clear HeqmB.
         revert ofs mA mB g g0; induction bytes; intros; simpl.
         -- simpl in *; omega.
         -- simpl length in g0; rewrite inj_S in g0.
            destruct (zeq ofs ofs0).
            ** subst ofs0. rewrite !Mem.setN_outside by omega. rewrite !ZMap.gss; auto.
            ** apply IHbytes; omega.
    * apply perm_le_cont. apply H.
  - assumption .
+ elim n; clear - PLE r. destruct PLE.
  red; intros. specialize (r _ H). specialize (perm_le_Cur b ofs0).
  unfold Mem.perm in *.
  destruct ((Mem.mem_access m1) !! b ofs0 Cur).
  destruct ((Mem.mem_access m) !! b ofs0 Cur). simpl in *. eapply perm_order_trans; eassumption.
  inv r.
  destruct ((Mem.mem_access m) !! b ofs0 Cur); inv perm_le_Cur. inv r.
Qed.

Lemma ple_loadbytes m b ofs n bytes
            (LD: Mem.loadbytes m b ofs n = Some bytes)
            m1 (PLE: perm_lesseq m m1) (N: 0 <= n):
            Mem.loadbytes m1 b ofs n = Some bytes.
Proof.
Transparent Mem.loadbytes.
unfold Mem.loadbytes.
Opaque Mem.loadbytes.
apply loadbytes_D in LD. destruct LD as [RP1 CONT].
destruct PLE.
destruct (Mem.range_perm_dec m1 b ofs (ofs + n) Cur Readable).
+ rewrite CONT; f_equal. eapply Mem.getN_exten.
  intros. apply perm_le_cont. apply RP1. rewrite nat_of_Z_eq in H; omega.
+ elim n0; clear - RP1 perm_le_Cur.
  red; intros. specialize (RP1 _ H). specialize (perm_le_Cur b ofs0).
  unfold Mem.perm in *.
  destruct ((Mem.mem_access m1) !! b ofs0 Cur).
  destruct ((Mem.mem_access m) !! b ofs0 Cur). simpl in *. eapply perm_order_trans; eassumption.
  inv RP1.
  destruct ((Mem.mem_access m) !! b ofs0 Cur); inv perm_le_Cur. inv RP1.
Qed.

Lemma alloc_access_inv m b lo hi m' (ALLOC: Mem.alloc m lo hi = (m', b)) b' ofs k p
  (P: (Mem.mem_access m') !! b' ofs k = Some p):
  (b'=b /\ Z.le lo ofs /\ Z.lt ofs hi) \/
  (b' <> b /\ (Mem.mem_access m) !! b' ofs k = Some p).
Proof.
Transparent Mem.alloc. unfold Mem.alloc in ALLOC. Opaque Mem.alloc. inv ALLOC; simpl in *.
rewrite PMap.gsspec in P.
destruct (peq b' (Mem.nextblock m)); subst; trivial.
+ left; split; trivial.
  remember (zle lo ofs && zlt ofs hi) as q. destruct q; inv P; trivial.
  destruct (zle lo ofs); destruct (zlt ofs hi); simpl in *; try discriminate; omega.
+ right; split; trivial.
Qed.

Lemma alloc_access_inv_None m b lo hi m' (ALLOC: Mem.alloc m lo hi = (m', b)) b' ofs k
  (P: (Mem.mem_access m') !! b' ofs k = None): (Mem.mem_access m) !! b' ofs k = None.
Proof.
Transparent Mem.alloc. unfold Mem.alloc in ALLOC. Opaque Mem.alloc. inv ALLOC; simpl in *.
rewrite PMap.gsspec in P.
destruct (peq b' (Mem.nextblock m)); subst; trivial.
apply Mem.nextblock_noaccess. xomega.
Qed.

Lemma alloc_inc_perm: forall m lo hi m' b
      (M: Mem.alloc m lo hi = (m',b)) m1 (PLE: perm_lesseq m m1),
      exists m1' : mem, Mem.alloc m1 lo hi =(m1',b) /\ perm_lesseq m' m1'.
Proof. intros.
  remember (Mem.alloc m1 lo hi). destruct p; symmetry in Heqp.
  assert (B: b0=b).
     apply Mem.alloc_result  in M. apply Mem.alloc_result  in Heqp.
     destruct PLE. rewrite perm_le_nb in *; subst. trivial.
  subst b0.
  eexists m0; split; trivial.
  Transparent Mem.alloc. unfold Mem.alloc in *. Opaque Mem.alloc. inv M; inv Heqp. simpl in *.
  destruct PLE.
  split; simpl; intros.
  + specialize (perm_le_Cur b ofs); clear perm_le_Max perm_le_cont.
    rewrite perm_le_nb, PMap.gsspec.  rewrite PMap.gsspec.
    destruct (peq b (Mem.nextblock m1)); subst; trivial.
    destruct (if zle lo ofs && zlt ofs hi then Some Freeable else None); simpl; trivial. apply perm_refl.
  + specialize (perm_le_Max b ofs); clear perm_le_Cur perm_le_cont.
    rewrite perm_le_nb, PMap.gsspec.  rewrite PMap.gsspec.
    destruct (peq b (Mem.nextblock m1)); subst; trivial.
    destruct (if zle lo ofs && zlt ofs hi then Some Freeable else None); simpl; trivial. apply perm_refl.
  + unfold Mem.perm in H; simpl in H.
    rewrite PMap.gsspec in H.
    destruct (peq b (Mem.nextblock m)); subst.
    - rewrite perm_le_nb. do 2 rewrite PMap.gss. trivial.
    - rewrite PMap.gso; try rewrite H1; trivial. rewrite PMap.gso; trivial. apply perm_le_cont. apply H.
  + rewrite H1; trivial.
Qed.

Lemma perm_lesseq_refl:
  forall m, perm_lesseq m m.
Proof.
intros.
 constructor; intros; auto.
 match goal with |- Mem.perm_order'' ?A _ => destruct A; constructor end.
 match goal with |- Mem.perm_order'' ?A _ => destruct A; constructor end.
Qed.

(*************************************************************************)

Definition corestep_fun {C M : Type} (sem : @CoreSemantics C M) :=
  forall (m m' m'' : M) c c' c'',
  corestep sem c m c' m' ->
  corestep sem c m c'' m'' ->
  c'=c'' /\ m'=m''.

(**  Multistepping *)

Section corestepN.
  Context {C M E:Type} (Sem:@CoreSemantics C M).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
      | O => fun c m c' m' => (c,m) = (c',m')
      | S k => fun c1 m1 c3 m3 => exists c2, exists m2,
        corestep Sem c1 m1 c2 m2 /\
        corestepN k c2 m2 c3 m3
    end.

  Lemma corestepN_add : forall n m c1 m1 c3 m3,
    corestepN (n+m) c1 m1 c3 m3 <->
    exists c2, exists m2,
      corestepN n c1 m1 c2 m2 /\
      corestepN m c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
    firstorder. firstorder.
    inv H. auto.
    decompose [ex and] H. clear H.
    destruct (IHn m x x0 c3 m3).
    apply H in H2.
    decompose [ex and] H2. clear H2.
    repeat econstructor; eauto.
    decompose [ex and] H. clear H.
    exists x1. exists x2; split; auto.
    destruct (IHn m x1 x2 c3 m3).
    eauto.
  Qed.

  Definition corestep_plus c m c' m' :=
    exists n, corestepN (S n) c m c' m'.

  Definition corestep_star c m c' m' :=
    exists n, corestepN n c m c' m'.

  Lemma corestep_plus_star : forall c1 c2 m1 m2,
    corestep_plus c1 m1 c2 m2 -> corestep_star c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma corestep_plus_trans : forall c1 c2 c3 m1 m2 m3,
    corestep_plus c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 ->
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add (S n1) (S n2) c1 m1 c3 m3) as [_ H].
    eexists. apply H. exists c2. exists m2. split; assumption.
  Qed.

  Lemma corestep_star_plus_trans : forall c1 c2 c3 m1 m2 m3,
    corestep_star c1 m1 c2 m2 -> corestep_plus c2 m2 c3 m3 ->
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add n1 (S n2) c1 m1 c3 m3) as [_ H].
    rewrite <- plus_n_Sm in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_plus_star_trans: forall c1 c2 c3 m1 m2 m3,
    corestep_plus c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 ->
    corestep_plus c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add (S n1) n2 c1 m1 c3 m3) as [_ H].
    rewrite plus_Sn_m in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_star_trans: forall c1 c2 c3 m1 m2 m3,
    corestep_star c1 m1 c2 m2 -> corestep_star c2 m2 c3 m3 ->
    corestep_star c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (corestepN_add n1 n2 c1 m1 c3 m3) as [_ H].
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma corestep_plus_one: forall c m c' m',
    corestep Sem c m c' m' -> corestep_plus c m c' m'.
  Proof. intros. unfold corestep_plus, corestepN. simpl.
    exists O. exists c'. exists m'. eauto.
  Qed.

  Lemma corestep_plus_two: forall c m c' m' c'' m'',
    corestep Sem c m c' m' -> corestep Sem c' m' c'' m'' ->
    corestep_plus c m c'' m''.
  Proof. intros.
    exists (S O). exists c'. exists m'. split; trivial.
    exists c''. exists m''. split; trivial. reflexivity.
  Qed.

  Lemma corestep_star_zero: forall c m, corestep_star  c m c m.
  Proof. intros. exists O. reflexivity. Qed.

  Lemma corestep_star_one: forall c m c' m',
    corestep  Sem c m c' m' -> corestep_star c m c' m'.
  Proof. intros.
    exists (S O). exists c'. exists m'. split; trivial. reflexivity.
  Qed.

  Lemma corestep_plus_split: forall c m c' m',
    corestep_plus c m c' m' ->
    exists c'', exists m'', corestep  Sem c m c'' m'' /\
      corestep_star c'' m'' c' m'.
  Proof. intros.
    destruct H as [n [c2 [m2 [Hstep Hstar]]]]. simpl in*.
    exists c2. exists m2. split. assumption. exists n. assumption.
  Qed.

End corestepN.

Section memstepN.
  Context {C:Type} (M:@MemSem C).

Lemma corestepN_mem n: forall c m c' m', corestepN M n c m c' m' -> mem_step m m'.
induction n; intros; inv H.
  apply mem_step_refl.
  destruct H0 as [m'' [CS CSN]]. eapply mem_step_trans.
  eapply corestep_mem; eassumption.
  eapply IHn; eassumption.
Qed.

Lemma corestep_plus_mem c m c' m' (H:corestep_plus M c m c' m'): mem_step m m'.
destruct H as [n H]. eapply corestepN_mem; eassumption. Qed.

Lemma corestep_star_mem c m c' m' (H:corestep_star M c m c' m'): mem_step m m'.
destruct H as [n H]. eapply corestepN_mem; eassumption. Qed.

Lemma memsem_preservesN P (HP: memstep_preserve P)
      n c m c' m' (H: corestepN M n c m c' m'): P m m'.
apply corestepN_mem in H. apply HP; trivial. Qed.

Lemma memsem_preserves_plus P (HP:memstep_preserve P)
      c m c' m' (H: corestep_plus M c m c' m'): P m m'.
destruct H. apply (memsem_preservesN _ HP) in H; trivial. Qed.

Lemma memsem_preserves_star P (HP:memstep_preserve P)
      c m c' m' (H: corestep_star M c m c' m'): P m m'.
destruct H. apply (memsem_preservesN _ HP) in H; trivial. Qed.

Lemma corestepN_fwd n  c m c' m'
   (CS:corestepN M n c m c' m'): mem_forward m m'.
Proof.
eapply memsem_preservesN; try eassumption. apply mem_forward_preserve.
Qed.

Lemma corestep_plus_fwd c m c' m'
   (CS:corestep_plus M c m c' m'): mem_forward m m'.
Proof.
destruct CS. eapply corestepN_fwd; eassumption.
Qed.

Lemma corestep_star_fwd c m c' m'
   (CS:corestep_star M c m c' m'): mem_forward m m'.
Proof.
destruct CS. eapply corestepN_fwd; eassumption.
Qed.

Lemma corestepN_rdonly n c m c' m'
    (CS:corestepN M n c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
eapply (memsem_preservesN _ readonly_preserve'); eassumption.
Qed.

Lemma corestep_plus_rdonly c m c' m'
   (CS:corestep_plus M c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
destruct CS. eapply corestepN_rdonly; eassumption.
Qed.

Lemma corestep_star_rdonly c m c' m'
   (CS:corestep_star M c m c' m')b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
destruct CS. eapply corestepN_rdonly; eassumption.
Qed.

End memstepN.
