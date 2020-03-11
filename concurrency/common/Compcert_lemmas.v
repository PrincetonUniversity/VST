
Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import VST.sepcomp.Address.

Require Import VST.concurrency.common.lksize.
Require Import VST.concurrency.common.mem_equiv.
Require Import  VST.concurrency.compiler.advanced_permissions.
Require Import  VST.concurrency.lib.tactics.
Import Ptrofs.
Import permissions.

Set Nested Proofs Allowed.

(* Lemmas in this file support the compiler proofs, 
   in particular concur_match.v and synchronisation_symulations.v.

   Its for files that depend only on CompCert definitions
 *)

Lemma list_inject_weaken: 
  forall j lev1 lev2,
    Events.list_inject_mem_effect_strong j lev1 lev2 ->
    Events.list_inject_mem_effect j lev1 lev2.
Proof.
  intros. induction H; subst; constructor.
  - apply Events.inj_mem_effect_strong_weak; assumption.
  - eauto.
Qed.

Lemma list_inject_mem_effect_cat:
  forall j l1 l1' l2 l2',
    Events.list_inject_mem_effect j l1 l2 ->
    Events.list_inject_mem_effect j l1' l2' ->
    Events.list_inject_mem_effect j (l1++l1') (l2++l2').
Proof. intros *. eapply Forall2_app. Qed.

Lemma address_inject_max:
  forall f m1 m2 b1 ofs1 b2 delta p,
    Mem.inject f m1 m2 ->
    Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max p ->
    f b1 = Some (b2, delta) ->
    unsigned (add ofs1 (Ptrofs.repr delta)) =
    unsigned ofs1 + delta.
Proof.
  intros.
  assert (Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty)
    by eauto with mem.
  exploit Mem.mi_representable; eauto. intros [A B].
  assert (0 <= delta <= Ptrofs.max_unsigned).
  generalize (Ptrofs.unsigned_range ofs1). omega.
  unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; omega.
Qed.


Lemma load_inject':
  forall (f : meminj) (m1 m2 : mem) (chunk : AST.memory_chunk)
    (b1 : block) (ofs : Z) (b2 : block) (delta : Z) 
         (v1 v2 : val),
    Mem.inject f m1 m2 ->
    Mem.load chunk m1 b1 ofs = Some v1 ->
    f b1 = Some (b2, delta) ->
    Val.inject f v1 v2 ->
    v1 <> Vundef ->
    Mem.load chunk m2 b2 (ofs + delta) = Some v2.
Proof.
  intros. exploit Mem.load_inject; eauto.
  intros (?&?&?).
  replace v2 with x; auto.
  clear - H3 H5 H2.
  inv H5; inv H2; auto.
  - unify_injection; reflexivity.
  -  congruence.
Qed.


Lemma address_inj_store':
  forall mu m1 m2' m1' b1 b2 ofs delt v,
    mu b1 = Some (b2, delt) ->
    Mem.inject mu m1' m2' ->
    Mem.store AST.Mint32 m1 b1 (unsigned ofs) v = Some m1' ->
    unsigned (add ofs (repr delt)) = unsigned ofs + delt.
Proof.
  intros * Hinj_b1 Hinj Hstore.
  eapply Mem.address_inject; eauto.
  
  eapply Mem.perm_store_1; eauto.
  eapply Mem.store_valid_access_3 in Hstore.
  destruct Hstore as [Hperm ?].
  specialize (Hperm (unsigned ofs)).
  eapply Hperm.
  replace unsigned with unsigned by reflexivity.
  pose proof (size_chunk_pos AST.Mint32).
  omega.
Qed.
Lemma address_inj_store:
  forall mu m1 m2 m1' b1 b2 ofs delt v,
    mu b1 = Some (b2, delt) ->
    Mem.inject mu m1 m2 ->
    Mem.store AST.Mint32 m1 b1 (unsigned ofs) (Vint v) = Some m1' ->
    unsigned (add ofs (repr delt)) = unsigned ofs + delt.
Proof.
  intros * Hinj_b1 Hinj Hstore.
  exploit Mem.store_mapped_inject; eauto.
  intros (?&_&?). clear Hinj.
  eapply address_inj_store'; eauto.
Qed.



Definition same_content_in m m' ofs b:=
  ZMap.get ofs (Mem.mem_contents m') !! b =
  ZMap.get ofs (Mem.mem_contents m) !! b.
Definition content_almost_same m m' adr:=
  forall  b ofs,
    b <> fst adr \/ ~ Intv.In ofs (snd adr,snd adr+ 4) ->
    same_content_in m m' ofs b.
Definition contnet_same_intval m m' adr SIZE:=
  forall b ofs,
    b = fst adr /\ Intv.In ofs (snd adr, snd adr + SIZE) ->
    same_content_in m m' ofs b.
Instance content_almost_same_proper:
  Proper (content_equiv ==> content_equiv ==> Logic.eq ==> iff)
         content_almost_same.
Proof.
  unfold content_almost_same, same_content_in.
  setoid_help.proper_iff;
    setoid_help.proper_intros; subst.
  
  rewrite <- H, <- H0; eauto.
Qed.

Definition get_vals_at (m:mem) (adr: block * Z):=
  (Mem.getN 4 (snd adr) (Mem.mem_contents m) !! (fst adr)).

Section LockUpdate.
  (* Lock update*)
  
Inductive lock_update_mem: mem -> Address.address -> list memval -> mem -> Prop:=
| Build_lock_update_mem:
    forall m m' adr v
      (Hcontent_almost_equiv: content_almost_same m m' adr)
      (Hnew_val: get_vals_at m' adr = v)
      (Hcur_equiv: Cur_equiv m m')
      (Hmax_equiv: getMaxPerm m = getMaxPerm m')
      (Hmax_wrt: max_valid_perm m AST.Mint32 (fst adr) (snd adr) Writable)
      (*Hmax_wrt: Mem.perm m (fst adr) (snd adr) Max Writable *)
      (Hnb_equiv: Mem.nextblock m = Mem.nextblock m'),
      lock_update_mem m adr v m'.


Lemma lock_update_mem_restr:
  forall m adr1 v1 m',
    lock_update_mem m adr1 v1 m' ->
    forall p p' Hlt Hlt',
      access_map_equiv p p' ->
      lock_update_mem (@restrPermMap p m Hlt)
                      adr1 v1 (@restrPermMap p' m' Hlt').
Proof.
  intros. inv H; econstructor; auto.
  - unfold Cur_equiv. do 2 rewrite getCur_restr; assumption.
  - unfold Max_equiv. do 2 rewrite getMax_restr_eq; assumption.
  - rewrite restr_Max_equiv; assumption.
Qed.

Lemma lock_update_mem_restr' p p':
  forall (m : mem) (adr1 : address) (v1 : list memval) (m' : mem)
    (Hlt : permMapLt p (getMaxPerm m))
    (Hlt' : permMapLt p' (getMaxPerm m')),
    lock_update_mem (restrPermMap Hlt) adr1 v1 (restrPermMap Hlt') ->
    Cur_equiv m m' ->
    lock_update_mem m adr1 v1 m'.
Proof.
  intros.
  rewrite (mem_is_restr_eq m), (mem_is_restr_eq m').
  erewrite (@restrPermMap_idempotent_eq _ _ m).
  erewrite (@restrPermMap_idempotent_eq _ _ m').
  eapply lock_update_mem_restr; eauto.
  Unshelve.
  all: intros ??; rewrite getMax_restr; apply mem_cur_lt_max.
Qed.       
Inductive lock_update_mem_strict b ofs m m': val -> Prop :=
| Build_lock_update_mem_strict:
    forall vstore
      (Haccess: Mem.range_perm m b ofs (ofs + LKSIZE) Cur Writable)
      (Hstore: Mem.store AST.Mint32 m b ofs vstore = Some m'),
      lock_update_mem_strict b ofs m m' vstore.
Lemma lock_update_mem_permMapLt_range_Cur:
  forall b ofs m m' v,
    lock_update_mem_strict b ofs m m' v -> 
    permMapLt_range (getCurPerm m) b ofs (ofs + LKSIZE) (Some Writable).
Proof.
  intros * HH; inv HH.
  eapply range_mem_permMapLt;  eassumption.
Qed.
Lemma lock_update_mem_permMapLt_range_Max:
  forall b ofs m m' v,
    lock_update_mem_strict b ofs m m' v -> 
    permMapLt_range (getMaxPerm m) b ofs (ofs + LKSIZE) (Some Writable).
Proof.
  intros; eapply permMapLt_range_trans; try eapply cur_lt_max.
  eapply lock_update_mem_permMapLt_range_Cur; eassumption.
Qed.
Inductive lock_update_mem_strict_load b ofs lock_perm m m': val -> val -> Prop :=
| Build_lock_update_mem_strict_load:
    forall lock_mem_lt vload vstore
      (Hwritable_lock1 : writable_lock b ofs lock_perm m),
      let lock_mem:= @restrPermMap lock_perm m lock_mem_lt in
      let m_writable_lock_1:= restrPermMap Hwritable_lock1 in
      forall (Haccess: Mem.range_perm lock_mem b ofs (ofs + LKSIZE) Cur Readable)
        (Hload: Mem.load AST.Mint32 lock_mem b ofs = Some vload)
        (Hstore: Mem.store AST.Mint32 m_writable_lock_1 b ofs vstore = Some m'),
        lock_update_mem_strict_load b ofs lock_perm m m' vload vstore.
Lemma lock_update_mem_strict_load_restr:
  forall b ofs l_perms m m' lval sval p Hlt,
    lock_update_mem_strict_load b ofs l_perms m m' lval sval ->
    lock_update_mem_strict_load b ofs l_perms (@restrPermMap p m Hlt) m' lval sval.
Proof.
  intros. inv H.
  unshelve econstructor.
  - rewrite restr_Max_eq; auto.
  - red. rewrite restr_Max_eq; auto.
  - rewrite <- restrPermMap_idempotent; eauto.
  - rewrite <- restrPermMap_idempotent; eauto.
  - erewrite <- restrPermMap_idempotent_eq; eauto.
Qed.
Lemma lock_update_mem_strict_inject:
  forall f b b' ofs delt m1 m2 m1' vl,
  forall (Hinj_b : f b = Some (b', delt))
    (Hinj_lock: Mem.inject f m1 m2),
    lock_update_mem_strict b ofs m1 m1' (Vint vl) ->
    exists m2', lock_update_mem_strict b' (ofs+ delt) m2 m2' (Vint vl) /\
           Mem.inject f m1' m2'.
Proof.
  intros; inv H.
  eapply Mem.store_mapped_inject in Hstore as (m2'&Hstore2&Hinj'); eauto.
  eexists; split; eauto.
  econstructor; eauto.
  replace (ofs + delt + LKSIZE) with ((ofs + LKSIZE) + delt).
  - eapply Mem.range_perm_inject; eauto.
  - omega.
Qed.
End LockUpdate.




Definition meminj_no_overlap_one (f: meminj) (m: mem) (adr1 adr2: block * Z) := 
  forall delta1 b1 delta2 ofs1,
    f (fst adr1) = Some (fst adr2, delta1) ->
    f b1 = Some (fst adr2, delta2) ->
    Mem.perm m b1 ofs1 Max Nonempty ->
    Intv.In (ofs1 + delta2) ((snd adr1) + delta1, (snd adr1) + delta1 + 4) ->
    (* ofs1 + delta2 = (snd adr1) + delta1 -> *)
    b1 = (fst adr1).
Lemma meminj_no_overlap_to_on:
  forall f m adr1 adr2,
    max_valid_perm m AST.Mint32 (fst adr1) (snd adr1) Writable ->
    Mem.meminj_no_overlap f m ->
    meminj_no_overlap_one f m adr1 adr2.
Proof.
  intros ** ? **.
  destruct (base.block_eq_dec b1 (fst adr1)); auto.
  exploit H0; eauto.
  { eapply Mem.perm_implies.
    eapply H. 2:constructor.
    unfold max_valid_perm, Mem.range_perm in H.
    instantiate(1:= ofs1 + delta2 - delta1).
    clear - H4. destruct H4. simpl in *. omega. }
  intros [ ? | ? ].
  - contradict H5; reflexivity.
  - contradict H5. omega. 
Qed.
Lemma adddress_eq_dec:
  forall (a b: block * Z), {a = b} + {a <> b}.
Proof.
  intros. destruct a as (a1& a2);
            destruct b as (b1& b2).
  destruct (base.block_eq_dec a1 b1) as [eq|n];
    destruct (Z.eq_dec a2 b2)as [eq'|n']; try subst;
      simpl in *; auto;
        try (right; intros HH; inv HH; try apply n; try apply n'; auto). 
Qed.
Lemma address_range_dec':
  forall (b b':block) ofs ofs' delta,
    (b = b' /\ Intv.In ofs (ofs', ofs' + delta))
    \/ (b <> b' \/ ~ Intv.In ofs (ofs', ofs' + delta)).
Proof.
  intros.
  cut (forall (P Q R:Prop), (P -> Q) -> (R \/ P)-> R \/ Q ); swap 1 2.
  { tauto. }
  intros HH. eapply HH.
  2: { eapply Classical_Prop.classic. }
  destruct (base.block_eq_dec b b'); auto.
Qed.
Lemma address_range_dec:
  forall (a1 a2: block * Z) delta,
    (fst a1 = fst a2 /\ Intv.In (snd a1)
                               (snd a2, snd a2 + delta))
    \/ (fst a1 <> fst a2 \/ ~ Intv.In (snd a1)
                           (snd a2, snd a2 + delta)).
Proof. intros; eapply address_range_dec'. Qed.

Lemma perm_order_trans101:
  forall oa b c, Mem.perm_order' oa b ->
            perm_order b c -> Mem.perm_order' oa c.
Proof.
  intros. eapply (perm_order_trans211 _ (Some b));
            simpl; auto.
Qed.
Lemma In_split: forall a b ofs,
    Intv.In ofs (a,b) ->
    Intv.In ofs (a+1,b) \/ ofs = a.
Proof. unfold Intv.In; simpl; intros; omega. Qed.


Inductive inject_address f: address -> address -> Prop :=
| build_inject_address:
    forall b1 b2 ofs1 ofs2 delt,
      f b1 = Some (b2, delt) ->
      ofs2 = ofs1 + delt ->
      inject_address f (b1, ofs1) (b2,ofs2).
Lemma inject_address_incr:
  forall f f' l1 l2,
    inject_incr f f' ->  
    inject_address f l1 l2 ->
    inject_address f' l1 l2.
Proof.
  intros * Hincr Hinj. inv Hinj.
  econstructor; auto.
  eapply Hincr; assumption.
Qed.



Lemma inj_getN_range:
  forall F f ofs ofs' b1 b2 delt m1 m2 LKSIZE,
    f b1 = Some (b2, delt) ->
    Intv.In ofs (ofs', ofs' + LKSIZE) ->
    Forall2 F
            (Mem.getN (Z.to_nat LKSIZE) ofs' (Mem.mem_contents m1) !! b1)
            (Mem.getN (Z.to_nat LKSIZE) (ofs' + delt) (Mem.mem_contents m2) !! b2) ->
    F (ZMap.get ofs (Mem.mem_contents m1) !! b1)
      (ZMap.get (ofs + delt) (Mem.mem_contents m2) !! b2).
Proof.
  induction LKSIZE; swap 2 3.
  - intros. exfalso; clear -H0.
    destruct H0; simpl in *. omega.
  - intros. exfalso; clear -H0.
    eapply Intv.in_notempty in H0.
    apply H0. unfold Intv.empty; simpl.
    pose proof (Zlt_neg_0 p). omega.
  - simpl. rewrite <- (Pos2Nat.id p).
    remember (Pos.to_nat p) as n.
    intros. replace (Pos.to_nat (Pos.of_nat n)) with n in *.
    2:{ subst n. rewrite Pos2Nat.id; auto. }
    revert H1 H0.
    destruct n.
    { exfalso; clear - Heqn. 
      pose proof (Pos2Nat.is_pos p).
      rewrite Heqn in *. omega. }
    clear Heqn.
    revert ofs ofs'. 
    induction n.
    + intros; simpl.
      simpl in H0.
      assert (ofs = ofs').
      { destruct H0. simpl in *. omega. }
      inv H1; auto. 
    + intros. simpl in H1; inv H1.
      replace (Z.pos (Pos.of_nat (S (S n)))) with
          (Z.pos (Pos.of_nat (S n)) + 1) in *.
      2:{  do 2 f_equal.
           symmetry; rewrite <- Pos.of_nat_succ .
           rewrite <- Pos.of_nat_succ.
           simpl. rewrite Pos.add_comm.
           simpl. destruct (Pos.of_succ_nat n); auto. }
      rewrite Z.add_assoc in H0.
      eapply In_split in H0.
      destruct H0; auto; swap 1 2.
      * subst; eauto.
      * clear H5.
        exploit IHn; eauto.
        2:{ instantiate(1:=ofs' +1).
            rewrite <- Z.add_assoc.
            rewrite (Z.add_comm 1).
            rewrite Z.add_assoc.
            eauto.
        }
        replace (ofs' + 1 + delt) with (ofs' + delt  + 1) by omega.
        auto.
Qed.
Lemma address_inj_lock_update:
  forall f b b' ofs delt m1 m1' m2' vs,
  forall (Hinj_b : f b = Some (b', delt)),
  forall (Hinj_lock: Mem.inject f m1' m2'),
    lock_update_mem_strict b (unsigned ofs) m1 m1' (Vint vs) ->
    unsigned (add ofs (repr delt)) = unsigned ofs + delt.
Proof.
  intros * Hinj_b Minj HH.
  inv HH; eapply address_inj_store'; eassumption.
Qed.
Lemma address_inj_lock_update_load:
  forall f b b' ofs delt perms1 m1 m1' m2' vl vs,
  forall (Hinj_b : f b = Some (b', delt)),
  forall (Hinj_lock: Mem.inject f m1' m2'),
    lock_update_mem_strict_load b (unsigned ofs) perms1 m1 m1' (Vint vl) (Vint vs) ->
    unsigned (add ofs (repr delt)) = unsigned ofs + delt.
Proof.
  intros * Hinj_b Minj HH.
  inv HH; eapply address_inj_store'; eassumption.
Qed.

Lemma store_almost_same:
  forall m b ofs vstore m',
    Mem.store AST.Mint32 m b ofs vstore = Some m' ->
    content_almost_same m m' (b, ofs).
Proof.
  intros * H0 ?? H1; unfold same_content_in.
  erewrite Mem.store_mem_contents; eauto;clear H0.
  destruct (base.block_eq_dec b b0) as [HH|HH]; subst.
  + destruct H1; try solve[exfalso; eauto].
    rewrite PMap.gss.
    rewrite Mem.setN_outside; auto.
    rewrite encode_val_length; simpl.
    unfold Mem.setN; simpl in *.
    eapply Intv.range_notin in H;
      simpl in *; omega.
  + clear H1. rewrite PMap.gso; eauto.
Qed.
(* HERE *)
Lemma lock_update_mem_strict_mem_update:
  forall b ofs m m' vstore,
    lock_update_mem_strict b ofs m m' vstore ->
    lock_update_mem m (b, ofs) (encode_val AST.Mint32 vstore) m'.
Proof.
  intros. inv H.
  econstructor.
  - eapply store_almost_same; eauto.
  - unfold get_vals_at.
    erewrite Mem.store_mem_contents; eauto.
    rewrite PMap.gss.
    make_abstract 4%nat.
    eapply Mem.getN_setN_same.
    rewrite encode_val_length; reflexivity.
  - eapply store_cur_equiv; eauto.
  - unfold getMaxPerm.
    erewrite <- Mem.store_access; eauto.
  - unfold max_valid_perm; simpl.
    exploit Mem.store_valid_access_3; eauto.
    intros (?&?) ? ?. apply Mem.perm_cur_max.
    eapply H; eauto.
  - symmetry; eapply Mem.nextblock_store; eauto.
Qed.
Lemma lock_update_mem_strict_load_mem_update:
  forall b ofs p m m' vload vstore,
    lock_update_mem_strict_load b ofs p m m' vload vstore ->
    Cur_equiv m m' ->
    lock_update_mem m (b, ofs) (encode_val AST.Mint32 vstore) m'.
Proof.
  intros. inv H.
  econstructor.
  - pose proof (restr_content_equiv Hwritable_lock1) as HH.
    symmetry in HH. 
    eapply content_almost_same_proper; eauto.
    reflexivity.
    eapply store_almost_same; eauto.
  - unfold get_vals_at.
    erewrite Mem.store_mem_contents; eauto.
    rewrite PMap.gss.
    make_abstract 4%nat.
    eapply Mem.getN_setN_same.
    rewrite encode_val_length; reflexivity.
  - eauto. 
  - symmetry; etransitivity.
    + unfold getMaxPerm.
      erewrite Mem.store_access; eauto.
    + symmetry; etransitivity.
      * symmetry; eapply getMax_restr_eq.
      * reflexivity.
  - unfold max_valid_perm; simpl.
    exploit Mem.store_valid_access_3; eauto.
    intros (?&?) ? ?. erewrite <- restr_Max_equiv.
    apply Mem.perm_cur_max.
    eapply H; eauto.
  - erewrite <- restrPermMap_nextblock.
    symmetry; eapply Mem.nextblock_store; eauto.
Qed.

Lemma lock_update_mem_strict_Max_equiv:
  forall b ofs m m' v1,
    lock_update_mem_strict b ofs m m' v1 ->
    Max_equiv m m'.
Proof.
  intros * HH; inversion HH; subst vstore.
  symmetry; eapply mem_access_max_equiv,  Mem.store_access.
  eauto.
Qed.
Lemma lock_update_mem_strict_load_Max_equiv:
  forall b ofs perms m m' v1 v2,
    lock_update_mem_strict_load b ofs perms m m' v1 v2 ->
    Max_equiv m m'.
Proof.
  intros * HH.
  inversion HH; subst vload vstore.
  subst m_writable_lock_1; eauto.
  etransitivity.
  - symmetry.
    eapply restr_Max_equiv.
  - apply mem_access_max_equiv.
    symmetry; eapply Mem.store_access; eauto.
Qed.


Lemma mem_simpl_eq:
  forall m1 m2,
    Mem.mem_contents m1 = Mem.mem_contents m2 ->
    Mem.mem_access m1 = Mem.mem_access m2 ->
    Mem.nextblock m1 = Mem.nextblock m2 ->
    m1 = m2.
Proof.
  intros. destruct m1; destruct m2.
  simpl in *.
  dependent_rewrite H.
  dependent_rewrite H0.
  dependent_rewrite H1.
  f_equal; eapply Axioms.proof_irr.
Qed.


Lemma self_restre_eq:
  forall p m Hlt,
    access_map_equiv p (getCurPerm m) ->
    @restrPermMap p m Hlt = m.
Proof.
  intros.
  eapply mem_simpl_eq; try reflexivity.
  pose proof (Cur_isCanonical m) as Hcanon.
  destruct m; simpl in *.
  clear Hlt.
  destruct mem_access; f_equal.
  - eapply (extensionality); intros ofs.
    eapply (extensionality); intros k.
    + destruct k; try reflexivity.
      hnf in Hcanon. unfold getCurPerm in Hcanon; simpl in *.
      eapply (f_equal) in Hcanon.
      instantiate(1:= fun x => x ofs) in Hcanon;
        simpl in *; auto.
  - simpl.
    eapply Coqlib3.PTree_map_eq.
    unfold option_map; intros.
    match_case. f_equal.
  - eapply (extensionality); intros ofs.
    eapply (extensionality); intros k.
    match_case.
    hnf in H; rewrite H.
    rewrite getCurPerm_correct; eauto;
      unfold permission_at; simpl.
    unfold "!!"; simpl. rewrite Heqo0; auto.
Qed.
Lemma restre_equiv_eq:
  forall p1 p2 m Hlt1 Hlt2,
    access_map_equiv p1 p2 ->
    @restrPermMap p1 m Hlt1 = @restrPermMap p2 m Hlt2.
Proof.
  intros.
  erewrite restrPermMap_idempotent_eq.
  erewrite self_restre_eq.
  - reflexivity.
  - symmetry. etransitivity.
    + eapply getCur_restr. 
    + symmetry; eauto.
      
      Unshelve.
      intros ? ?;
      rewrite getMax_restr; eauto.
Qed.
Lemma lock_update_mem_strict_cur:
  forall b ofs m m' v,
    lock_update_mem_strict b ofs m m' v ->
    Cur_equiv m m'.
Proof.
  intros. inv H. intros ?.
  eapply store_cur_equiv; eauto.
Qed.


Lemma mem_inj_update:
  forall (f:meminj) m1 m2 m1' m2' adr1 adr2
    (Hno_overlap:
       meminj_no_overlap_one f m1 adr1 adr2)
    (Hmax_eq1: Max_equiv m1 m1')
    (Hmax_eq2: Max_equiv m2 m2')
    (Hcur_eq1: Cur_equiv m1 m1')
    (Hcur_eq2: Cur_equiv m2 m2')
    (Hadr_inj: inject_address f adr1 adr2)
    (Halmost1: content_almost_same m1 m1' adr1)
    (Halmost2: content_almost_same m2 m2' adr2)
    (Hsame12: (Forall2 (memval_inject f))
                (get_vals_at m1' adr1) (get_vals_at m2' adr2))
    (Hmem_inj: Mem.mem_inj f m1 m2),
    Mem.mem_inj f m1' m2'.
Proof.
  econstructor; intros.
  - destruct k;
      first [rewrite <- Hmax_eq2 |rewrite <- Hcur_eq2];
      eapply Hmem_inj; eauto;
        first [rewrite Hmax_eq1 |rewrite Hcur_eq1];
        assumption.
  - eapply Hmem_inj; eauto.
    rewrite Hmax_eq1; eassumption.
  - rewrite <- Hcur_eq1 in H0.
    unfold get_vals_at in Hsame12.
    destruct (address_range_dec (b1, ofs) adr1 4).
    (*destruct (adddress_eq_dec (b1, ofs) adr1). *)
    + (* (b1,ofs) \in (adr1, adr1+LKSIZE) *)
      simpl in H1; destruct H1; subst.
      (*subst adr1; eauto.*)
      inv Hadr_inj. simpl in *; unify_injection.
      eapply inj_getN_range; eauto.
    + (*eapply getN_content_equiv in Halmost1.*)
      (* (b1,ofs) \not \in (adr1, adr1+LKSIZE) *)
      simpl in H1. destruct (peq b1 (fst adr1)).
      * subst; destruct H1 as [H1 | H1];
          try solve [exfalso; apply H1; auto].
        erewrite Halmost1; eauto.
        erewrite Halmost2; eauto.
        2:{ right. inv Hadr_inj; simpl in *.
            unify_injection. clear - H1.
            intros [HH1 HH2]; eapply H1; split; simpl in *.
            omega. clear - HH2.
            rewrite <- Z.add_assoc in HH2.
            rewrite (Z.add_comm delt) in HH2.
            rewrite Z.add_assoc in HH2. 
            omega.
        }
        eapply Hmem_inj; eauto.
      * clear H1.
        erewrite Halmost1; eauto.
        destruct (address_range_dec (b2, ofs + delta) adr2 (size_chunk AST.Mint32)).
        -- (* (b2,ofs+delta) \in (adr2, adr2+LKSIZE) *)
          destruct H1; subst.
          inv Hadr_inj.
          simpl snd in Hsame12.
          simpl fst in Hsame12.
          simpl in H1, n , H3; inv H1.
          exploit (Hno_overlap delt b1); simpl; eauto.
          ++ eapply Mem.perm_cur_max, Mem.perm_implies; eauto; constructor.
          ++ intros HH; contradict n; auto.
             
        -- rewrite Halmost2; eauto.
           eapply Hmem_inj; eauto.
Qed.

Lemma injection_update:
  forall f m1 m2 m1' m2' adr1 adr2
    (Hnonempty: max_valid_perm m1 AST.Mint32 (fst adr1) (snd adr1) Writable)
    (Hsame_nb1: Mem.nextblock m1 = Mem.nextblock m1')
    (Hsame_nb2: Mem.nextblock m2 = Mem.nextblock m2')
    (Hmax_eq1: Max_equiv m1 m1')
    (Hmax_eq2: Max_equiv m2 m2')
    (Hcur_eq1: Cur_equiv m1 m1')
    (Hcur_eq2: Cur_equiv m2 m2')
    (Hadr_inj: inject_address f adr1 adr2)
    (Halmost1: content_almost_same m1 m1' adr1)
    (Halmost2: content_almost_same m2 m2' adr2)
    (Hsame12: Forall2 (memval_inject f)
                      (get_vals_at m1' adr1) (get_vals_at m2' adr2))
    (Hmem_inj: Mem.inject f m1 m2),
    Mem.inject f m1' m2'.
Proof.
  econstructor; intros.
  - eapply mem_inj_update; try eassumption. 2: apply Hmem_inj.
    eapply meminj_no_overlap_to_on. 2: apply Hmem_inj.
    auto.
  - eapply Hmem_inj.
    unfold Mem.valid_block in *. rewrite Hsame_nb1; assumption.
  - unfold Mem.valid_block; rewrite <- Hsame_nb2.
    eapply Hmem_inj; eassumption.
  - rewrite <- Hmax_eq1. apply Hmem_inj.
  - eapply Hmem_inj; eauto.
    rewrite Hmax_eq1; auto.
  - destruct k;
      first [rewrite <- Hmax_eq2 in H0 |rewrite <- Hcur_eq2 in H0];
      eapply Hmem_inj in H0; eauto.
    + rewrite <- Hmax_eq1; auto.
    + destruct H0; 
        first [left; rewrite <- Hcur_eq1;assumption |right; rewrite <- Hmax_eq1; assumption].
Qed.

Lemma full_inj_restr:
  forall mu m p,
    Events.injection_full mu m ->
    forall (Hlt: permMapLt p (getMaxPerm m)), 
      Events.injection_full mu (restrPermMap Hlt).
Proof.
  intros ** ? **. eapply H.
  unshelve  eapply restrPermMap_valid; eauto.
Qed.

