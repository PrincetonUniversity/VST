Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST. 
Require Import compcert.common.Globalenvs.
Require Import msl.Extensionality. 

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.semantics.

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
  destruct Q as [Q1 Q2]. destruct W as [W1 W2].
  split; intros.
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

Lemma memsem_preserves {G C} (s: @MemSem G C) P (HP:memstep_preserve P):
      forall g c m c' m', corestep s g c m c' m'-> P m m'.
Proof. intros.
  apply corestep_mem in H.
  eapply preserve_mem; eassumption.
Qed.

Lemma corestep_fwd {C G} (s:@MemSem G C) g c m c' m'
   (CS:corestep s g c m c' m' ): mem_forward m m'.
Proof.
eapply memsem_preserves; try eassumption. apply mem_forward_preserve.
Qed.

Lemma corestep_rdonly {C G} (s:@MemSem G C) g c m c' m'
   (CS:corestep s g c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
eapply (memsem_preserves s _ readonly_preserve'); eassumption.
Qed.

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

(*************************************************************************)

Definition corestep_fun {G C M : Type} (sem : CoreSemantics G C M) :=
  forall (m m' m'' : M) ge c c' c'',
  corestep sem ge c m c' m' -> 
  corestep sem ge c m c'' m'' -> 
  c'=c'' /\ m'=m''.

(**  Multistepping *)

Section corestepN.
  Context {G C M E:Type} (Sem:CoreSemantics G C M) (ge:G).

  Fixpoint corestepN (n:nat) : C -> M -> C -> M -> Prop :=
    match n with
      | O => fun c m c' m' => (c,m) = (c',m')
      | S k => fun c1 m1 c3 m3 => exists c2, exists m2,
        corestep Sem ge c1 m1 c2 m2 /\
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
    corestep  Sem ge c m c' m' -> corestep_plus c m c' m'.
  Proof. intros. unfold corestep_plus, corestepN. simpl.
    exists O. exists c'. exists m'. eauto. 
  Qed.

  Lemma corestep_plus_two: forall c m c' m' c'' m'',
    corestep  Sem ge c m c' m' -> corestep  Sem ge c' m' c'' m'' -> 
    corestep_plus c m c'' m''.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. 
    exists c''. exists m''. split; trivial. reflexivity.
  Qed.

  Lemma corestep_star_zero: forall c m, corestep_star  c m c m.
  Proof. intros. exists O. reflexivity. Qed.

  Lemma corestep_star_one: forall c m c' m',
    corestep  Sem ge c m c' m' -> corestep_star c m c' m'.
  Proof. intros. 
    exists (S O). exists c'. exists m'. split; trivial. reflexivity. 
  Qed.

  Lemma corestep_plus_split: forall c m c' m',
    corestep_plus c m c' m' ->
    exists c'', exists m'', corestep  Sem ge c m c'' m'' /\ 
      corestep_star c'' m'' c' m'.
  Proof. intros.
    destruct H as [n [c2 [m2 [Hstep Hstar]]]]. simpl in*. 
    exists c2. exists m2. split. assumption. exists n. assumption.  
  Qed.

End corestepN.

Section memstepN.
  Context {G C:Type} (M:@MemSem G C) (g:G).

Lemma corestepN_mem n: forall c m c' m', corestepN M g n c m c' m' -> mem_step m m'.
induction n; intros; inv H.
  apply mem_step_refl.
  destruct H0 as [m'' [CS CSN]]. eapply mem_step_trans. 
  eapply corestep_mem; eassumption.
  eapply IHn; eassumption.
Qed.

Lemma corestep_plus_mem c m c' m' (H:corestep_plus M g c m c' m'): mem_step m m'.
destruct H as [n H]. eapply corestepN_mem; eassumption. Qed.

Lemma corestep_star_mem c m c' m' (H:corestep_star M g c m c' m'): mem_step m m'.
destruct H as [n H]. eapply corestepN_mem; eassumption. Qed.

Lemma memsem_preservesN P (HP: memstep_preserve P)
      n c m c' m' (H: corestepN M g n c m c' m'): P m m'.
apply corestepN_mem in H. apply HP; trivial. Qed. 

Lemma memsem_preserves_plus P (HP:memstep_preserve P)
      c m c' m' (H: corestep_plus M g c m c' m'): P m m'.
destruct H. apply (memsem_preservesN _ HP) in H; trivial. Qed.

Lemma memsem_preserves_star P (HP:memstep_preserve P)
      c m c' m' (H: corestep_star M g c m c' m'): P m m'.
destruct H. apply (memsem_preservesN _ HP) in H; trivial. Qed.

Lemma corestepN_fwd n  c m c' m'
   (CS:corestepN M g n c m c' m'): mem_forward m m'.
Proof.
eapply memsem_preservesN; try eassumption. apply mem_forward_preserve.
Qed.

Lemma corestep_plus_fwd c m c' m'
   (CS:corestep_plus M g c m c' m'): mem_forward m m'.
Proof.
destruct CS. eapply corestepN_fwd; eassumption.
Qed.

Lemma corestep_star_fwd c m c' m'
   (CS:corestep_star M g c m c' m'): mem_forward m m'.
Proof.
destruct CS. eapply corestepN_fwd; eassumption.
Qed.
 
Lemma corestepN_rdonly n c m c' m'
    (CS:corestepN M g n c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
eapply (memsem_preservesN _ readonly_preserve'); eassumption.
Qed.

Lemma corestep_plus_rdonly c m c' m'
   (CS:corestep_plus M g c m c' m') b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
destruct CS. eapply corestepN_rdonly; eassumption.
Qed.

Lemma corestep_star_rdonly c m c' m'
   (CS:corestep_star M g c m c' m')b (VB:Mem.valid_block m b): readonly m b m'.
Proof.
destruct CS. eapply corestepN_rdonly; eassumption.
Qed.
 
End memstepN.
