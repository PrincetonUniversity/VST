Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.extspec.

Definition mem_lessdef m1 m2 :=
  (forall b ofs len v,
      Mem.loadbytes m1 b ofs len = Some v ->
      exists v',
        Mem.loadbytes m2 b ofs len = Some v' /\
        list_forall2 memval_lessdef v v'
  ) /\
  (forall b ofs k p,
      Mem.perm m1 b ofs k p ->
      Mem.perm m2 b ofs k p) /\
  (Mem.nextblock m1 <=
   Mem.nextblock m2)%positive.

Definition mem_lessalloc m1 m2 :=
  Mem.loadbytes m1 = Mem.loadbytes m2 /\
  Mem.perm m1 = Mem.perm m2 /\
  (Mem.nextblock m1 <= Mem.nextblock m2)%positive.

Definition mem_equiv m1 m2 :=
  Mem.loadbytes m1 = Mem.loadbytes m2 /\
  Mem.perm m1 = Mem.perm m2 /\
  Mem.nextblock m1 = Mem.nextblock m2.

Lemma same_perm_spec m1 m2 :
  Mem.perm m1 = Mem.perm m2 <->
  (forall k x, access_at m1 x k = access_at m2 x k).
Proof.
  split; intros E.
  - intros k (b, ofs).
    match type of E with ?f = ?g => assert (S : forall b z k p, f b z k p <-> g b z k p) end.
    { rewrite E; tauto. } clear E.
    spec S b ofs k. revert S.
    unfold access_at, Mem.perm. simpl.
    set (o1 := (Mem.mem_access _) !! b ofs k).
    set (o2 := (Mem.mem_access _) !! b ofs k). clearbody o1 o2. intros S.
    assert (S' : forall o, Mem.perm_order'' o1 o <-> Mem.perm_order'' o2 o).
    { intros [ o | ]. apply S. destruct o1 as [o1 | ], o2 as [o2 | ]; split; intro; constructor. }
    clear S.
    destruct (S' o1) as [A _]. spec A. apply perm_order_pp_refl.
    destruct (S' o2) as [_ B]. spec B. apply perm_order_pp_refl.
    destruct o1 as [[]|], o2 as [[]|]; auto; simpl in *.
    all: inv A; inv B; auto.
  - extensionality b ofs k. spec E k (b, ofs).
    unfold access_at in *.
    simpl in E.
    unfold Mem.perm in *.
    rewrite E.
    auto.
Qed.

Lemma same_loadbytes_spec m1 m2 :
  Mem.perm m1 = Mem.perm m2 ->  (* TODO change this to only need same Cur *)
  Mem.loadbytes m1 = Mem.loadbytes m2 <->
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x).
Proof.
  intros P; split; intros E.
  - intros (b, ofs) R.
    Transparent Mem.loadbytes.
    unfold Mem.loadbytes in *.
    apply equal_f with (x := b) in E.
    apply equal_f with (x := ofs) in E.
    apply equal_f with (x := 1) in E.
    unfold access_at in *.
    if_tac [p1|np1] in E; if_tac in E; try discriminate.
    + simpl in E.
      unfold contents_at in *.
      simpl.
      congruence.
    + destruct np1.
      intros ofs1 r1.
      cut (ofs1 = ofs). intros <-. apply R.
      omega.
  - extensionality b ofs k.
    unfold Mem.loadbytes in *.
    if_tac [p1|np1]; if_tac [p2|np2].
    + destruct (zle 0 k).
      * clear p2.
        f_equal.
        rewrite <-(Coqlib.nat_of_Z_eq k) in p1. 2:omega.
        revert p1. generalize (nat_of_Z k); clear k l; intros n.
        revert ofs.
        induction n; auto; intros ofs p.
        simpl. f_equal.
        -- spec E (b, ofs).
           unfold contents_at in *.
           simpl in E.
           apply E.
           apply p.
           simpl.
           zify; omega.
        -- apply IHn.
           intros ofs' r'.
           apply p.
           zify. omega.
      * rewrite nat_of_Z_neg. auto. omega.
    + destruct np2.
      unfold Mem.range_perm in *.
      rewrite <-P.
      auto.
    + destruct np1.
      unfold Mem.range_perm in *.
      rewrite P.
      auto.
    + auto.
Qed.

Definition mem_equiv' m1 m2 :=
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x) /\
  Mem.perm m1 = Mem.perm m2 /\
  Mem.nextblock m1 = Mem.nextblock m2.

Definition mem_lessalloc' m1 m2 :=
  (forall x, Mem.perm_order' (access_at m1 x Cur) Readable -> contents_at m1 x = contents_at m2 x) /\
  Mem.perm m1 = Mem.perm m2 /\
  (Mem.nextblock m1 <= Mem.nextblock m2)%positive.

Lemma mem_equiv'_spec m1 m2 : mem_equiv m1 m2 <-> mem_equiv' m1 m2.
Proof.
  split; intros (? & ? & ?); repeat split; auto.
  rewrite <-same_loadbytes_spec; auto.
  rewrite same_loadbytes_spec; auto.
Qed.

Lemma mem_lessalloc'_spec m1 m2 : mem_lessalloc m1 m2 <-> mem_lessalloc' m1 m2.
Proof.
  split; intros (? & ? & ?); repeat split; auto.
  rewrite <-same_loadbytes_spec; auto.
  rewrite same_loadbytes_spec; auto.
Qed.

Lemma val_inject_antisym v1 v2 :
  val_inject inject_id v1 v2 ->
  val_inject inject_id v2 v1 ->
  v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; try subst; try congruence.
  unfold inject_id in *.
  f_equal. congruence.
  replace delta with 0%Z by congruence.
  symmetry; apply Ptrofs.add_zero.
Qed.

Lemma memval_lessdef_antisym v1 v2 : memval_lessdef v1 v2 -> memval_lessdef v2 v1 -> v1 = v2.
Proof.
  destruct v1, v2; intros A B; auto.
  all: inversion A; subst; inversion B; subst; try congruence.
  f_equal. apply val_inject_antisym; auto.
Qed.

Lemma mem_lessdef_equiv m1 m2 : mem_lessdef m1 m2 -> mem_lessdef m2 m1 ->  mem_equiv m1 m2.
Proof.
  intros (L1 & P1 & N1) (L2 & P2 & N2); repeat split.
  - clear -L1 L2.
    extensionality b ofs z.
    match goal with |- ?a = ?b => destruct a as [v1|] eqn:E1; destruct b as [v2|] eqn:E2 end;
      try destruct (L1 _ _ _ _ E1) as (v2' & E1' & l1);
      try destruct (L2 _ _ _ _ E2) as (v1' & E2' & l2);
      try congruence.
    assert (v1' = v1) by congruence; assert (v2' = v2) by congruence; subst; f_equal.
    clear -l1 l2.
    revert v2 l1 l2; induction v1; intros v2 l1 l2; inversion l1; subst; auto.
    inversion l2; subst.
    f_equal; auto.
    apply memval_lessdef_antisym; auto.
  - repeat extensionality.
    apply prop_ext; split; auto.
  - zify.
    cut (Z.pos (Mem.nextblock m2) = Z.pos (Mem.nextblock m1)).
    congruence. omega.
Qed.

Lemma mem_equiv_refl m : mem_equiv m m.
Proof.
  split3; hnf; auto.
Qed.

Lemma mem_lessalloc_refl m : mem_lessalloc m m.
Proof.
  split3; auto. apply Ple_refl.
Qed.

Lemma mem_equiv_refl' m m' : m = m' -> mem_equiv m m'.
Proof.
  intros <-; apply mem_equiv_refl.
Qed.

Lemma mem_lessalloc_refl' m m' : m = m' -> mem_lessalloc m m'.
Proof.
  intros <-; apply mem_lessalloc_refl.
Qed.

Lemma mem_equiv_sym m1 m2 : mem_equiv m1 m2 -> mem_equiv m2 m1.
Proof.
  intros []; split; intuition.
Qed.

Lemma mem_equiv_trans m1 m2 m3 :
  mem_equiv m1 m2 ->
  mem_equiv m2 m3 ->
  mem_equiv m1 m3.
Proof.
  unfold mem_equiv in *.
  intros (-> & -> & ->) (-> & -> & ->); auto.
Qed.

Lemma mem_lessalloc_trans m1 m2 m3 :
  mem_lessalloc m1 m2 ->
  mem_lessalloc m2 m3 ->
  mem_lessalloc m1 m3.
Proof.
  unfold mem_lessalloc in *.
  intros (-> & -> & l) (-> & -> & l'); split; auto. split; auto.
  eapply Ple_trans; eauto.
Qed.

Lemma mem_equiv_lessalloc m1 m2 : mem_equiv m1 m2 -> mem_lessalloc m1 m2.
Proof.
  intros (L1 & P1 & N1); repeat split; auto.
  rewrite N1; auto. apply Ple_refl.
Qed.

Lemma mem_lessalloc_lessdef m1 m2 : mem_lessalloc m1 m2 -> mem_lessdef m1 m2.
Proof.
  intros (L1 & P1 & N1); repeat split.
  - rewrite L1; auto.
    intros b ofs len v H.
    exists v; intuition.
    clear.
    induction v; constructor; auto.
    apply memval_lessdef_refl.
  - rewrite P1; auto.
  - auto.
Qed.

Lemma mem_equiv_lessdef m1 m2 : mem_equiv m1 m2 -> mem_lessdef m1 m2.
Proof.
  intro H.
  apply mem_lessalloc_lessdef, mem_equiv_lessalloc, H.
Qed.

Lemma cl_step_mem_lessdef_sim {ge c m1 c' m1' m2} :
  mem_lessdef m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_lessdef m1' m2' /\
    @cl_step ge c m2 c' m2'.
Admitted.

Lemma eval_expr_mem_lessaloc {ge ve te m a v}:
  eval_expr ge ve te m a v ->
  forall m2 (L : mem_lessalloc m m2),
  eval_expr ge ve te m2 a v.
Admitted.

Lemma valid_pointer_lessalloc {m m2} (M:mem_lessalloc m m2):
      Mem.valid_pointer m = Mem.valid_pointer m2.
Proof. unfold Mem.valid_pointer. destruct M as [M1 [M2 M3]].
  extensionality b. extensionality i.
  destruct (Mem.perm_dec m b i Cur Nonempty);
  destruct (Mem.perm_dec m2 b i Cur Nonempty); trivial.
  exfalso. rewrite M2 in p. contradiction.
  exfalso. rewrite M2 in n. contradiction.
Qed.

Lemma weak_valid_pointer_lessalloc {m m2} (M:mem_lessalloc m m2):
      Mem.weak_valid_pointer m = Mem.weak_valid_pointer m2.
Proof.
  unfold Mem.weak_valid_pointer.
  extensionality b. extensionality i.
  rewrite (valid_pointer_lessalloc M); trivial.
Qed.

Lemma unaryop_mem_lessaloc {op u t m v m2}
      (V: sem_unary_operation op u t m = Some v)
      (M:mem_lessalloc m m2):
      sem_unary_operation op u t m2 = Some v.
Proof. destruct op; simpl; inv V; try econstructor.
unfold sem_notbool.
unfold bool_val.
remember (classify_bool t) as c.
destruct c; trivial.
destruct u; trivial.
rewrite (weak_valid_pointer_lessalloc M); trivial.
Qed.

Lemma sem_cast_mem_lessaloc {v t d m m2} (M:mem_lessalloc m m2):
      sem_cast v t d m = sem_cast v t d m2.
Proof.
unfold sem_cast.
destruct (classify_cast t d); trivial.
destruct v; trivial.
rewrite (weak_valid_pointer_lessalloc M); trivial.
Qed.

Lemma sem_cmp_mem_lessalloc {f v1 t1 v2 t2 m m2} (M : mem_lessalloc m m2):
      sem_cmp f v1 t1 v2 t2 m2 = sem_cmp f v1 t1 v2 t2 m.
Proof. unfold sem_cmp, cmp_ptr.
  destruct (classify_cmp t1 t2);
  try solve [destruct Archi.ptr64; rewrite (valid_pointer_lessalloc M); trivial].
 unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
Qed.

Lemma binaryop_mem_lessaloc {ge op v1 t1 v2 t2 m v m2}
      (V: sem_binary_operation ge op v1 t1 v2 t2 m = Some v)
      (M:mem_lessalloc m m2):
      sem_binary_operation ge op v1 t1 v2 t2 m2 = Some v.
Proof. destruct op; simpl; inv V; try econstructor; clear -M.
+ unfold sem_add.
  remember (classify_add t1 t2) as c.
  destruct c.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_sub.
  remember (classify_sub t1 t2) as c.
  destruct c.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - destruct v1; trivial.
  - unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_mul.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_div.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_mod.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_and.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_or.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_xor.
  unfold sem_binarith.
  do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ unfold sem_cmp, cmp_ptr.
  destruct (classify_cmp t1 t2);
  try solve [destruct Archi.ptr64; rewrite (valid_pointer_lessalloc M); trivial].
 unfold sem_binarith.
    do 2 rewrite (sem_cast_mem_lessaloc M); trivial.
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
+ apply (sem_cmp_mem_lessalloc M).
Qed.

Lemma eval_expr_eval_lvalue_mem_lessalloc ge ve te m:
     (forall (e : expr) (v : val),
        eval_expr ge ve te m e v ->
        forall m2 : mem, mem_lessalloc m m2 -> eval_expr ge ve te m2 e v) /\
     (forall (e : expr) (b : block) (i : ptrofs),
        eval_lvalue ge ve te m e b i ->
        forall m2 : mem, mem_lessalloc m m2 -> eval_lvalue ge ve te m2 e b i).
Proof. apply eval_expr_lvalue_ind; intros; try solve [econstructor; eauto].
+ econstructor; eauto. eapply unaryop_mem_lessaloc; eauto.
+ econstructor; eauto. eapply binaryop_mem_lessaloc; eauto.
+ econstructor; eauto. rewrite <- H1. symmetry. apply sem_cast_mem_lessaloc; trivial.
+ econstructor; eauto.
  destruct H2 as [M1 [M2 M3]].
  inv H1; simpl in *.
  - eapply deref_loc_value; eauto.
    simpl. destruct (Mem.load_loadbytes _ _ _ _ _ H3) as [vals [X Y]]; subst.
    rewrite M1 in X. apply Mem.load_valid_access in H3. destruct H3.
    eapply Mem.loadbytes_load; trivial.
  - apply deref_loc_reference; trivial.
  - apply deref_loc_copy; trivial.
Qed.

Lemma eval_expr_mem_lessalloc {ge ve te m m2 e v} (M:mem_lessalloc m m2):
      eval_expr ge ve te m e v -> eval_expr ge ve te m2 e v.
Proof. intros. eapply eval_expr_eval_lvalue_mem_lessalloc; eauto. Qed.

Lemma eval_exprlist_mem_lessalloc {ge ve te}:
      forall al tyargs vargs m m2 (M:mem_lessalloc m m2)
             (E:eval_exprlist ge ve te m al tyargs vargs),
      eval_exprlist ge ve te m2 al tyargs vargs.
Proof.
  induction al; simpl; intros; inv E.
   econstructor.
   apply (eval_expr_mem_lessalloc M) in H1.
   rewrite (sem_cast_mem_lessaloc M) in H2. econstructor; eauto.
Qed.

Lemma eval_lvalue_mem_lessalloc {ge ve te m m2 e b i} (M:mem_lessalloc m m2):
      eval_lvalue ge ve te m e b i -> eval_lvalue ge ve te m2 e b i.
Proof. intros. eapply eval_expr_eval_lvalue_mem_lessalloc; eauto. Qed.

Lemma storebytes_mem_lessalloc {m loc ofs bytes m' m2} (M:mem_lessalloc m m2)
      (ST:Mem.storebytes m loc ofs bytes = Some m'):
      exists m2', Mem.storebytes m2 loc ofs bytes = Some m2' /\
                  mem_lessalloc m' m2'.
Proof.
destruct M as [M1 [M2 M3]].
destruct (Mem.range_perm_storebytes m2 loc ofs bytes) as [m2' ST2].
{ red; intros. rewrite <- M2. eapply Mem.storebytes_range_perm; eassumption. }
exists m2'; split; trivial.
split; [| split].
+ extensionality b. extensionality z. extensionality n.
  (*should hold -here's a partial proof*)
  destruct (zlt n 0).
  - rewrite Mem.loadbytes_empty; try omega. rewrite Mem.loadbytes_empty; try omega. trivial.
  - destruct (eq_block loc b); subst.
    * destruct (zle (z + n) ofs).
      ++ rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ ST); auto.
         rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ ST2); auto.
         rewrite M1; trivial.
      ++ destruct (zle (ofs + Z.of_nat (Datatypes.length bytes)) z).
         -- rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ ST); auto.
            rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ ST2); auto.
            rewrite M1; trivial.
         -- (*should be ok specialize Z.le_exists_sub. assert (exists k, ofs = z+n-k /\ k>0).*) admit. (*rewrite (Mem.loadbytes_concat m' b z )*)
    * rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ ST); auto.
      rewrite (Mem.loadbytes_storebytes_other _ _ _ _ _ ST2); auto.
      rewrite M1; trivial.
+ apply Mem.storebytes_access in ST. apply Mem.storebytes_access in ST2.
  extensionality b. extensionality z. extensionality k. extensionality p.
  unfold Mem.perm. rewrite ST, ST2.
  assert (Mem.perm m b z k p = Mem.perm m2 b z k p). rewrite M2; trivial.
  apply H.
+ apply Mem.nextblock_storebytes in ST. apply Mem.nextblock_storebytes in ST2.
  rewrite ST, ST2. xomega.
Admitted.

Lemma free_mem_lessalloc m b lo hi m' (FR:Mem.free m b lo hi = Some m')
      m2 (M:mem_lessalloc m m2):
      exists m2', Mem.free m2 b lo hi = Some m2' /\ mem_lessalloc m' m2'.
Proof.
specialize (Mem.free_range_perm _ _ _ _ _ FR); intros RP.
apply Mem.free_result in FR. subst m'.
destruct M as [M1 [M2 M3]].
destruct (Mem.range_perm_free m2 b lo hi) as [m2' FR'].
{ red; intros. rewrite <- M2. apply RP; trivial. }
exists m2'; split; trivial.
apply Mem.free_result in FR'. subst m2'.
split; [|split]; simpl; trivial.
+ admit. (*loadbytes -- should be ok*)
+ unfold Mem.unchecked_free, Mem.perm; simpl. extensionality bb.
  extensionality z. extensionality k. extensionality p.
  do 2 rewrite PMap.gsspec.
  destruct (peq bb b); subst.
  assert (Mem.perm m b z k p = Mem.perm m2 b z k p). rewrite M2; trivial.
  clear M2. destruct (zle lo z && zlt z hi); trivial.
  assert (Mem.perm m bb z k p = Mem.perm m2 bb z k p). rewrite M2; trivial.
  trivial.
Admitted.

Lemma freelist_mem_lessalloc: forall l m m' (FR:Mem.free_list m l = Some m')
      m2 (M:mem_lessalloc m m2),
      exists m2', Mem.free_list m2 l = Some m2' /\ mem_lessalloc m' m2'.
Proof.
  induction l; simpl; intros.
+ inv FR. exists m2; split; trivial.
+ destruct a as [[b lo] hi]. remember (Mem.free m b lo hi) as q.
  destruct q; inv FR; symmetry in Heqq.
  specialize (IHl _ _ H0); clear H0.
  destruct (free_mem_lessalloc _ _ _ _ _ Heqq _ M) as [m2' [FR2 M2]].
  rewrite FR2; eauto.
Qed.

Lemma store_mem_lessalloc {m chunk b ofs v m' m2} (M:mem_lessalloc m m2)
      (ST:Mem.store chunk m b ofs v = Some m'):
      exists m2', Mem.store chunk m2 b ofs v = Some m2' /\
                  mem_lessalloc m' m2'.
Proof.
 exploit Mem.store_storebytes; eauto. intros.
 apply Mem.store_valid_access_3 in ST. destruct ST.
 apply (storebytes_mem_lessalloc M) in H.
 destruct H as [m2' [ST2 M2]].
 exists m2'; split; trivial.
 apply Mem.storebytes_store; eauto.
Qed.

Lemma assign_loc_mem_lessalloc {ge t m loc ofs v m' m2} (M:mem_lessalloc m m2):
      assign_loc ge t m loc ofs v m' ->
      exists m2', mem_lessalloc m' m2' /\ assign_loc ge t m2 loc ofs v m2'.
Proof. destruct 1; simpl in *.
+ destruct (store_mem_lessalloc M H0) as [m2' [ST2 M2]].
  exists m2'; split; eauto. eapply assign_loc_value; eauto.
+ destruct (storebytes_mem_lessalloc M H4) as [m2' [ST2 M2']].
  destruct M as [M1 [M2 M3]]. rewrite M1 in H3.
  exists m2'; split; trivial.
  eapply assign_loc_copy; eauto.
Qed.

Lemma alloc_variables_mem_lessalloc {ge ve}: forall vars e m m1
      (A:alloc_variables ge e m vars ve m1) m' (M:mem_lessalloc m m'),
      exists m1', alloc_variables ge e m' vars ve m1' /\ mem_lessalloc m1 m1'.
Proof. intros vars e m m1 A.
  induction A; intros.
+ exists m'; split; eauto. constructor.
+ remember (sizeof ty) as sz.
  remember (Mem.alloc m' 0 sz). destruct p as [m1' b1']. symmetry in Heqp.
  (*2 issues: a) mem_lessalloc m1 m1' does not necessarily hold
              b) if b1<>b1', id will be set different in the two executions*)
  (*Maybe it's possible to egenralize the statement of this lemma suitably...*)
(*  destruct (IHA _ H0) as [m2' [X Y]]. subst sz.
  exists m2'; split; trivial. econstructor. eauto. *)
Admitted.

Lemma cl_step_mem_lessalloc_sim {ge c m1 c' m1' m2} :
  mem_lessalloc m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_lessalloc m1' m2' /\
    @cl_step ge c m2 c' m2'.
(* we cannot use [cl_step_mem_lessdef_sim] directly because
[mem_lessalloc] does not imply [mem_lessdef] in both
directions. However, the proof must be simpler. *)
Proof.
intros M STEP. generalize dependent m2.
induction STEP; intros.
+ apply (eval_expr_mem_lessalloc M) in H1.
  apply (eval_lvalue_mem_lessalloc M) in H0.
  rewrite (sem_cast_mem_lessaloc M) in H2.
  destruct (assign_loc_mem_lessalloc M H3) as [m2' [M2' ASS2]].
  exists m2'; split; trivial. econstructor; eauto.
+ exists m2; split; trivial.
  apply (eval_expr_mem_lessalloc M) in H. constructor; trivial.
+ apply (eval_expr_mem_lessalloc M) in H0.
  apply (eval_exprlist_mem_lessalloc _ _ _ _ _ M) in H1.
  (* here - we have the same initial ve in both cases, so I think
     it'll be difficult to generalize the alloc_variables lemma above suitably*)
  destruct (alloc_variables_mem_lessalloc _ _ _ _ H5 _ M) as [m2' [AV' M']].
  exists m2'; split; trivial.
  econstructor; eauto.
+ exists m2; split; trivial.
  apply (eval_expr_mem_lessalloc M) in H0.
  apply (eval_exprlist_mem_lessalloc _ _ _ _ _ M) in H1.
  econstructor; eauto.
+ destruct (IHSTEP _ M) as [m2' [L' STEP']].
  exists m2'; split; trivial. econstructor; eassumption.
+ destruct (IHSTEP _ M) as [m2' [L' STEP']].
  exists m2'; split; trivial. econstructor; eassumption.
+ destruct (IHSTEP _ M) as [m2' [L' STEP']].
  exists m2'; split; trivial. econstructor; eassumption.
+ destruct (IHSTEP _ M) as [m2' [L' STEP']].
  exists m2'; split; trivial. econstructor; eassumption.
+ exists m2; split; trivial.
  apply (eval_expr_mem_lessalloc M) in H.
  econstructor; eauto.
  unfold bool_val in *. destruct (classify_bool (typeof a)); trivial.
  destruct v1; trivial. rewrite <- (weak_valid_pointer_lessalloc M); trivial.
+ exists m2; split; trivial. econstructor.
+ exists m2; split; trivial. constructor.
+ destruct (freelist_mem_lessalloc _ _ _ H0 _ M) as [m2' [FL2 M2]].
  exists m2'; split; trivial. econstructor; eauto.
  destruct optexp; trivial.
  destruct H1 as [v [E SC]]. apply (eval_expr_mem_lessalloc M) in E.
  rewrite (sem_cast_mem_lessaloc M) in SC.
  exists v; split; trivial.
+ exists m2; split; trivial.
  apply (eval_expr_mem_lessalloc M) in H.
  econstructor; eauto.
+ destruct (IHSTEP _ M) as [m2' [L' STEP']].
  exists m2'; split; trivial. econstructor; eassumption.
+ exists m2; split; trivial. econstructor; eauto.
Qed.

Lemma cl_step_mem_equiv_sim {ge c m1 c' m1' m2} :
  mem_equiv m1 m2 ->
  @cl_step ge c m1 c' m1' ->
  exists m2',
    mem_equiv m1' m2' /\
    @cl_step ge c m2 c' m2'.
Proof.
  intros E S1.
  pose proof mem_equiv_lessdef _ _ E as L12.
  pose proof mem_equiv_lessdef _ _ (mem_equiv_sym _ _ E) as L21.
  destruct (cl_step_mem_lessdef_sim L12 S1) as (m2' & L12' & S2).
  destruct (cl_step_mem_lessdef_sim L21 S2) as (m1'' & L21' & S1').
  exists m2'; split; auto.
  apply mem_lessdef_equiv; auto.
  cut (m1'' = m1'). intros <-; auto.
  pose proof semax_lemmas.cl_corestep_fun' ge _ _ _ _ _ _ S1 S1'.
  congruence.
Qed.

Definition juicy_mem_equiv jm1 jm2 := mem_equiv (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Definition juicy_mem_lessdef jm1 jm2 := mem_lessdef (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Definition juicy_mem_lessalloc jm1 jm2 := mem_lessdef (m_dry jm1) (m_dry jm2) /\ m_phi jm1 = m_phi jm2.

Lemma mem_equiv_juicy_mem_equiv jm1 m2 :
  mem_equiv (m_dry jm1) m2 ->
  exists jm2,
    m_dry jm2 = m2 /\
    juicy_mem_equiv jm1 jm2.
Proof.
  intros E.
  refine (ex_intro _ (mkJuicyMem m2 (m_phi jm1) _ _ _ _) _); repeat (split; auto).
  Unshelve.
  all: destruct jm1 as [m1 phi Con Acc Max All]; simpl in *.
  all: destruct E as (Load & Perm & Next).
    (* I'll admit this for now. It should take less time to prove once
    the new mem interface is there. *)
Admitted.

Lemma mem_lessdef_juicy_mem_lessdef jm1 m2 :
  mem_lessdef (m_dry jm1) m2 ->
  exists jm2,
    m_dry jm2 = m2 /\
    juicy_mem_lessdef jm1 jm2.
Proof.
  (* not sure about that one! [contents_cohere] should be ok, but
  [access_cohere] does not have a reason to be *)
Admitted.

Lemma mem_lessalloc_juicy_mem_lessdef jm1 m2 :
  mem_lessalloc (m_dry jm1) m2 ->
  exists jm2,
    m_dry jm2 = m2 /\
    juicy_mem_lessalloc jm1 jm2.
Proof.
  (* this one is fine, we need to prove that if two memories are
  mem_lessalloc then the difference of nextblock is only None's *)
Admitted.

Lemma juicy_step_mem_equiv_sim {ge c jm1 c' jm1' jm2} :
  juicy_mem_equiv jm1 jm2 ->
  corestep (juicy_core_sem cl_core_sem) ge c jm1 c' jm1' ->
  exists jm2',
    juicy_mem_equiv jm1' jm2' /\
    corestep (juicy_core_sem cl_core_sem) ge c jm2 c' jm2'.
Proof.
  intros [Ed Ew] [step [rd lev]].
  destruct (cl_step_mem_equiv_sim Ed step) as [m2' [Ed' Sd']].
  destruct (mem_equiv_juicy_mem_equiv jm1' m2' Ed') as (jm2', (<-, [Hd Hw])).
  exists jm2'.
  split; split; auto. split.
  - cut (Mem.nextblock (m_dry jm1) = Mem.nextblock (m_dry jm2)). congruence.
    apply Ed.
  - repeat rewrite level_juice_level_phi in *.
    congruence.
Qed.

Ltac sync D :=
  first
    [ split; [destruct D as [D _] | destruct D as [_ D]]
    | destruct D as [D|D]; [left|right]
    | let x := fresh in destruct D as (x, D); exists x
    | let x := fresh in intro x; spec D x
    ].

Lemma juicy_step_mem_lessdef_sim {ge c jm1 c' jm1' jm2} :
  juicy_mem_lessdef jm1 jm2 ->
  corestep (juicy_core_sem cl_core_sem) ge c jm1 c' jm1' ->
  exists jm2',
    juicy_mem_lessdef jm1' jm2' /\
    corestep (juicy_core_sem cl_core_sem) ge c jm2 c' jm2'.
Proof.
  intros [Ed Ew] [step D].
  destruct (cl_step_mem_lessdef_sim Ed step) as [m2' [Ed' Sd']].
  destruct (mem_lessdef_juicy_mem_lessdef jm1' m2' Ed') as (jm2', (<-, [Hd Hw])).
  exists jm2'.
  split; split; auto.
  repeat rewrite level_juice_level_phi in *.

  repeat sync D.

  all: try rewrite <-Ew; try rewrite <-Hw; try assumption.

  - intros out. apply D.
    unfold mem_lessdef in *.
    zify.
    omega.

  - unfold mem_lessdef in *.
    zify.
    Fail omega. (* not true, maybe we can still resource_decay them somehow *)
Admitted.

Definition ext_spec_stable {M E Z} (R : M -> M -> Prop)
           (spec : external_specification M E Z) :=
  (forall e x b tl vl z m1 m2,
    R m1 m2 ->
    ext_spec_pre spec e x b tl vl z m1 ->
    ext_spec_pre spec e x b tl vl z m2) /\
  (forall e v m1 m2,
    R m1 m2 ->
    ext_spec_exit spec e v m1 ->
    ext_spec_exit spec e v m2).

(* Currently fails because jsafeN__ind is too weak.

Lemma jsafeN_mem_equiv {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_equiv jm1 jm2 ->
  ext_spec_stable juicy_mem_equiv (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof.
  intros E [Spre Sexit] S1.
  revert jm2 E.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 E.

  - constructor 1.

  - destruct (juicy_step_mem_equiv_sim E step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.

  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct E as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.

  - econstructor 4; eauto.
Qed.

Lemma jsafeN_mem_lessdef {Z Jspec ge n z c jm1 jm2} :
  juicy_mem_lessdef jm1 jm2 ->
  ext_spec_stable juicy_mem_lessdef (JE_spec _ Jspec) ->
  @jsafeN Z Jspec ge n z c jm1 ->
  @jsafeN Z Jspec ge n z c jm2.
Proof.
  intros L [Spre Sexit] S1.
  revert jm2 L.
  induction S1 as
      [ z c jm1
      | n z c jm1 c' jm1' step safe IH
      | n z c jm1 ef args x atex Pre Post
      | n z c jm1 v Halt Exit ]; intros jm2 L.

  - constructor 1.

  - destruct (juicy_step_mem_lessdef_sim L step) as (jm2' & E' & step').
    econstructor 2; eauto.
    apply IH, E'.

  - econstructor 3 with (x := x); eauto.
    intros ret jm2' z' n' Hargsty Hretty Hn [-> [lev pure]] post.
    destruct (Post ret jm2' z' _ Hargsty Hretty Hn) as (c' & atex' & safe'); auto.
    + split; auto.
      destruct L as [Ed Ew].
      unfold juicy_safety.pures_eq in *.
      unfold juicy_safety.pures_sub in *.
      split.
      * repeat rewrite level_juice_level_phi in *.
        congruence.
      * revert pure.
        rewrite Ew.
        auto.
    + exists c'; split; auto.

  - econstructor 4; eauto.
Qed.*)

Lemma mem_ext m1 m2 :
  Mem.mem_contents m1 = Mem.mem_contents m2 ->
  Mem.mem_access m1 = Mem.mem_access m2 ->
  Mem.nextblock m1 = Mem.nextblock m2 ->
  m1 = m2.
Proof.
  destruct m1, m2; simpl in *.
  intros <- <- <- .
  f_equal; apply proof_irr.
Qed.
