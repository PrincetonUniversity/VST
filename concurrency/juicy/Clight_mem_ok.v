Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import VST.concurrency.common.permissions.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_core.
Require Import VST.concurrency.juicy.mem_wd2.
Require Import VST.msl.eq_dec.
Require Import BinNums.
Require Import List. Import ListNotations.
Require Import VST.msl.Coqlib2.
Require VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.common.threadPool.
Set Bullet Behavior "Strict Subproofs".
Import Memory.
Import ThreadPool.

Arguments sizeof {env} t.

Section GE.

Variable ge: Clight.genv.

Definition maxedmem (m: mem) :=
  restrPermMap (mem_max_lt_max m).

Definition mem_wellformed (m: mem) :=
 Mem.inject_neutral (Mem.nextblock m) (maxedmem m) /\
  Ple (Genv.genv_next ge) (Mem.nextblock m).

Lemma access_at_restr_Cur: 
 forall loc p m Hlt, access_at (@restrPermMap p m Hlt) loc Cur =  p !! (fst loc) (snd loc).
Proof.
intros.
destruct loc.
rewrite <- restrPermMap_Cur with (m:=m) (Hlt:=Hlt).
reflexivity.
Qed.

Lemma access_at_restr_Max: 
 forall loc p m Hlt, access_at (@restrPermMap p m Hlt) loc Max =  access_at m loc Max.
Proof.
intros.
destruct loc.
simpl.
change (permission_at (restrPermMap Hlt) b z Max = permission_at m b z Max).
rewrite restrPermMap_Max.
unfold getMaxPerm.
rewrite PMap.gmap.
reflexivity.
Qed.

Lemma access_at_maxedmem: 
 forall k m loc, access_at (maxedmem m) loc k =  access_at m loc Max.
Proof.
intros.
destruct loc.
unfold maxedmem.
destruct k.
apply access_at_restr_Max.
rewrite access_at_restr_Cur.
unfold getMaxPerm.
rewrite PMap.gmap.
reflexivity.
Qed.

Lemma maxedmem_neutral:
  forall m,
 Mem.inject_neutral (Mem.nextblock (maxedmem m)) (maxedmem m) ->
  Mem.inject_neutral (Mem.nextblock m) m.
Proof.
intros.
unfold Mem.inject_neutral in *.
inv H.
constructor; intros; simpl in *.
-
unfold Mem.flat_inj in H.
if_tac in H; inv H.
rewrite Z.add_0_r. auto.
-
eapply mi_align; eauto.
intros ? ?.
unfold maxedmem.
rewrite mem_equiv.restr_Max_equiv. eauto.
-
apply mi_memval; auto.
clear - H0.
rewrite perm_access in H0.
rewrite perm_access.
eapply perm_order''_trans; try eassumption.
clear H0.
rewrite access_at_maxedmem.
apply access_cur_max.
Qed.

Lemma mem_equiv_restr_max:
 forall m j (k: permMapLt j (getMaxPerm m)),
mem_equiv.mem_equiv (restrPermMap (mem_max_lt_max (@restrPermMap j m k)))
  (restrPermMap (mem_max_lt_max m)).
Proof.
intros.
constructor.
-
red.
etransitivity.
apply mem_equiv.getCur_restr.
fold (maxedmem m).
intro b.
extensionality z.
rewrite getCurPerm_correct.
rewrite getMaxPerm_correct.
unfold permission_at.
symmetry.
pose proof (access_at_maxedmem Cur m (b,z)).
unfold access_at in H.
simpl fst in H; simpl snd in H.
rewrite H.
symmetry.
pose proof (restrPermMap_Max k b z).
unfold permission_at in H0.
rewrite getMaxPerm_correct in H0.
apply H0.
-
rewrite !mem_equiv.restr_Max_equiv.
reflexivity.
-
rewrite !mem_equiv.restr_content_equiv.
reflexivity.
-
reflexivity.
Qed.


Section CTL_OK.
  Variable nextb : block.
Definition val_wellformed (v: val) : Prop :=
   Val.inject (Mem.flat_inj nextb) v v.

Definition block_wellformed (b: block) := Plt b nextb.

Definition venv_wellformed (ve: Clight.env) :=
  forall i bt, PTree.get i ve = Some bt -> block_wellformed (fst bt).

Definition tenv_wellformed (te: Clight.temp_env) :=
  forall i (v: val), PTree.get i te = Some v -> val_wellformed v.

Fixpoint cont_wellformed (k: cont) := 
 match k with
 | Kstop _ => True
 | Kseq _ k' => cont_wellformed k'
 | Kloop1 _ _ k' => cont_wellformed k'
 | Kloop2 _ _ k' => cont_wellformed k'
 | Kswitch k' => cont_wellformed k'
 | Kcall _ _ ve te k' => venv_wellformed ve /\ tenv_wellformed te /\ cont_wellformed k'
 end.

Definition core_wellformed (q: Clight_core.state) : Prop :=
 match q with
 | Clight_core.State _ _ k ve te => venv_wellformed ve /\ tenv_wellformed te /\ cont_wellformed k
 | Clight_core.Callstate f args k =>
       Forall val_wellformed args /\  cont_wellformed k
 | Clight_core.Returnstate v k => val_wellformed v /\ cont_wellformed k
 end.

End CTL_OK.

Definition ctl_wellformed {res : semantics.Resources} {sem: semantics.Semantics}
   (core_wellformed: block -> semantics.semC -> Prop)
    m ctl :=
 match ctl with
    | Krun q => core_wellformed (Mem.nextblock m) q
    | Kblocked q => core_wellformed (Mem.nextblock m) q
                              /\ semantics.at_external (semantics.csem (msem (@semantics.semSem sem))) q m <> None
    | Kresume q v => core_wellformed (Mem.nextblock m) q /\ semantics.at_external (semantics.csem (msem (@semantics.semSem sem))) q m <> None /\ v = Vundef
    | Kinit v1 v2 => val_wellformed (Mem.nextblock m) v1 /\ val_wellformed (Mem.nextblock m) v2
    end.

Definition threads_wellformed
   {res : semantics.Resources} {sem: semantics.Semantics}
   {core_wellformed: block -> semantics.semC -> Prop}
   m tp  :=
  forall i (cnti : @containsThread res sem OrdinalPool.OrdinalThreadPool tp i),
     ctl_wellformed core_wellformed m (getThreadC cnti).

End GE.

Section ALLOC_OK.
Variable nextb: positive.
Variable nextb': positive.
Variable LESS:  (nextb <= nextb')%positive.

Lemma alloc_block_wellformed: forall b, block_wellformed nextb b -> block_wellformed nextb' b.
Proof.
intros.
red in H|-*. eapply Pos.lt_le_trans; eauto.
Qed.

Lemma alloc_val_wellformed: forall v, val_wellformed nextb v -> val_wellformed nextb' v.
Proof.
intros; destruct v; try solve [constructor].
hnf in H|-*.
inv H; apply Val.inject_ptr with delta; auto.
unfold Mem.flat_inj in *.
destruct (plt b nextb); inv H3.
rewrite if_true; auto.
eapply Plt_Ple_trans; eauto.
Qed.

Lemma alloc_venv_wellformed: forall ve, venv_wellformed nextb ve -> venv_wellformed nextb' ve.
Proof.
intros.
red in H|-*; intros.
eapply alloc_block_wellformed; eauto.
Qed.

Lemma alloc_tenv_wellformed: forall te, tenv_wellformed nextb te -> tenv_wellformed nextb' te.
Proof.
intros.
red in H|-*; intros.
eapply alloc_val_wellformed; eauto.
Qed.

Lemma alloc_cont_wellformed: forall k, cont_wellformed nextb k -> cont_wellformed nextb' k.
Proof.
induction k; simpl; intros; auto.
destruct H as [? [? ?]]. split3; auto.
eapply alloc_venv_wellformed; eauto.
eapply alloc_tenv_wellformed; eauto.
Qed.

Lemma alloc_core_wellformed: forall q, 
    core_wellformed nextb q -> core_wellformed nextb' q.
Proof.
destruct q; simpl.
intros [? [? ?]]; split; [|split].
eapply alloc_venv_wellformed; eauto.
eapply alloc_tenv_wellformed; eauto.
eapply alloc_cont_wellformed; eauto.
intros [? ?]; split.
eapply Forall_impl; try eassumption. apply alloc_val_wellformed.
apply alloc_cont_wellformed; auto.
intros [? ?]; split.
eapply alloc_val_wellformed; eauto.
apply alloc_cont_wellformed; auto.
Qed.

End ALLOC_OK.

Lemma alloc_ctl_wellformed: forall {res : semantics.Resources} {sem: semantics.Semantics}
    (cwf: block -> semantics.semC -> Prop)
   (H: forall (b b': block) (L: (b <= b')%positive) q, cwf b q -> cwf b' q)
   (Hat: forall s m m', 
   semantics.at_external (semantics.csem semantics.semSem) s m =
   semantics.at_external (semantics.csem semantics.semSem) s m')
    m m' c, 
    Ple (Mem.nextblock m) (Mem.nextblock m') ->
    ctl_wellformed cwf m c -> ctl_wellformed cwf m' c.
Proof.
intros.
destruct c; simpl in *; decompose [and] H1; repeat split; eauto;
try eapply alloc_val_wellformed; eauto;
erewrite <- Hat; eauto.
Qed.

Lemma set_tenv_wellformed:
  forall nextb i (v: val) te, val_wellformed nextb v -> tenv_wellformed nextb te ->
            tenv_wellformed nextb (PTree.set i v te).
Proof.
intros.
hnf in H0|-*.
intros.
destruct (eq_dec i i0).
subst. rewrite PTree.gss in H1. inv H1. auto.
rewrite PTree.gso in H1 by auto.
apply H0 in H1. auto.
Qed.

Lemma set_venv_wellformed:
  forall nextb i v ve, block_wellformed nextb (fst v) -> venv_wellformed nextb ve ->
            venv_wellformed nextb (PTree.set i v ve).
Proof.
intros.
hnf in H0|-*.
intros.
destruct (eq_dec i i0).
subst. rewrite PTree.gss in H1. inv H1. auto.
rewrite PTree.gso in H1 by auto.
apply H0 in H1. auto.
Qed.

Lemma sem_add_ptr_int_wellformed:
  forall ge nextb ty si v1 v2 v,
  val_wellformed nextb v1 ->
  val_wellformed nextb v2 ->
  Cop.sem_add_ptr_int (genv_cenv ge) ty si v1 v2 = Some v -> 
  val_wellformed nextb v.
Proof.
intros.
unfold Cop.sem_add_ptr_int in H1.
destruct v1; try discriminate;
destruct v2; try discriminate.
destruct Archi.ptr64; inv H1.
constructor.
inv H1.
inv H.
apply Val.inject_ptr with delta; auto.
apply mem_lemmas.flatinj_E in H4. destruct H4 as [? [? ?]]; subst.
rewrite Ptrofs.add_zero. auto.
Qed.

Lemma sem_add_ptr_long_wellformed:
  forall ge nextb ty v1 v2 v,
  val_wellformed nextb v1 ->
  val_wellformed nextb v2 ->
  Cop.sem_add_ptr_long (genv_cenv ge) ty v1 v2 = Some v -> 
  val_wellformed nextb v.
Proof.
intros.
unfold Cop.sem_add_ptr_long in H1.
destruct v1; try discriminate;
destruct v2; try discriminate.
destruct Archi.ptr64; inv H1. constructor.
inv H1.
inv H.
apply Val.inject_ptr with delta; auto.
apply mem_lemmas.flatinj_E in H4. destruct H4 as [? [? ?]]; subst.
rewrite Ptrofs.add_zero. auto.
Qed.

Lemma sem_cast_wellformed:
  forall nextb v1 t1 t2 m v,
    val_wellformed nextb v1 ->
    Cop.sem_cast v1 t1 t2 m = Some v ->
     val_wellformed nextb v.
Proof.
intros.
unfold Cop.sem_cast in H0.
destruct (Cop.classify_cast t1 t2); try discriminate;
destruct v1; try discriminate;
try solve [inv H0; auto; constructor].
destruct (Cop.cast_float_int si2 f); inv H0; try constructor.
destruct (Cop.cast_single_int si2 f); inv H0; try constructor.
destruct (Cop.cast_float_long si2 f); inv H0; try constructor.
destruct (Cop.cast_single_long si2 f); inv H0; try constructor.
destruct Archi.ptr64; inv H0; auto; try constructor.
destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); inv H2; try constructor.
if_tac in H0; inv H0; auto.
if_tac in H0; inv H0; auto.
Qed.

Lemma val_of_bool_wellformed:
  forall nextb b, val_wellformed nextb (Val.of_bool b).
Proof.
intros. destruct b; hnf; constructor.
Qed.

Lemma sem_cmp_wellformed: 
  forall nextb op v1 t1 v2 t2 m v,
 Cop.sem_cmp op v1 t1 v2 t2 m = Some v ->
 val_wellformed nextb v1 -> val_wellformed nextb v2 -> val_wellformed nextb v.
Proof.
intros.
pose proof (val_of_bool_wellformed nextb).
unfold Cop.sem_cmp in H.
destruct (Cop.classify_cmp t1 t2); try discriminate.
unfold Cop.cmp_ptr in H.
try match type of H with _ _ ?X = _ => destruct X; inv H; auto end.
destruct v2; try discriminate.
unfold Cop.cmp_ptr in H.
try match type of H with _ _ ?X = _ => destruct X; inv H; auto end.
destruct Archi.ptr64; try discriminate.
unfold Cop.cmp_ptr in H.
try match type of H with _ _ ?X = _ => destruct X; inv H; auto end.
destruct v1; try discriminate.
unfold Cop.cmp_ptr in H.
try match type of H with _ _ ?X = _ => destruct X; inv H; auto end.
destruct Archi.ptr64; try discriminate.
unfold Cop.cmp_ptr in H.
try match type of H with _ _ ?X = _ => destruct X; inv H; auto end.
destruct v2; try discriminate.
unfold Cop.cmp_ptr in H.
try match type of H with _ _ ?X = _ => destruct X; inv H; auto end.
destruct v1; try discriminate.
unfold Cop.cmp_ptr in H.
try match type of H with _ _ ?X = _ => destruct X; inv H; auto end.
unfold Cop.sem_binarith in H.
destruct (Cop.sem_cast v1 t1
        (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
destruct (Cop.sem_cast v2 t2
        (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
eapply sem_cast_wellformed in Heqo; eauto.
eapply sem_cast_wellformed in Heqo0; eauto.
destruct (Cop.classify_binarith t1 t2); try discriminate.
destruct v0;  try discriminate.
destruct v3;  try discriminate.
inv H; auto.
destruct v0;  try discriminate.
destruct v3;  try discriminate.
inv H; auto.
destruct v0;  try discriminate.
destruct v3;  try discriminate.
inv H; auto.
destruct v0;  try discriminate.
destruct v3;  try discriminate.
inv H; auto.
Qed.

Lemma binary_operation_wellformed:
forall ge nextb (op : Cop.binary_operation) (v1 : val) (t1 : type) 
  (v2 : val) (t2 : type) (m : mem) (v : val),
  val_wellformed nextb v1 ->
  val_wellformed nextb v2 ->
  Cop.sem_binary_operation (Clight.genv_cenv ge) op v1 t1 v2 t2 m = Some v ->
  val_wellformed nextb v.
Proof.
intros.
 destruct op; simpl in *;
   try solve [revert H1 H H0; apply sem_cmp_wellformed];
try solve [
  match type of H1 with ?A _ _ _ _ _ = _ => unfold A in H1 end;
   unfold Cop.sem_binarith in H1;
   destruct (Cop.sem_cast v1 t1
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate;
   destruct (Cop.sem_cast v2 t2
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate;
   eapply sem_cast_wellformed in Heqo; eauto;
   eapply sem_cast_wellformed in Heqo0; eauto;
   destruct (Cop.classify_binarith t1 t2); try discriminate;
   try solve [destruct v0; inv H1; destruct v3; inv H3; constructor];
   destruct v0; inv H1; destruct v3; inv H3; destruct s; inv H2;
   revert H3; simple_if_tac; intro H3; inv H3; constructor].
- unfold Cop.sem_add in H1.
   destruct (Cop.classify_add t1 t2);
   try solve [eapply sem_add_ptr_int_wellformed; try eapply H1; eauto];
   try solve [eapply sem_add_ptr_long_wellformed; try eapply H1; eauto].
   unfold Cop.sem_binarith in H1.
   destruct (Cop.sem_cast v1 t1
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   destruct (Cop.sem_cast v2 t2
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   eapply sem_cast_wellformed in Heqo; eauto.
   eapply sem_cast_wellformed in Heqo0; eauto.
   destruct (Cop.classify_binarith t1 t2); try discriminate;
   try solve [destruct v0; inv H1; destruct v3; inv H3; constructor].
- unfold Cop.sem_sub in H1.
   destruct (Cop.classify_sub t1 t2).
   destruct v1; try discriminate; 
   destruct v2; try discriminate; destruct Archi.ptr64; try discriminate; inv H1; auto; try constructor;
   inv H; econstructor; eauto;
   apply mem_lemmas.flatinj_E in H4; destruct H4 as [? [? ?]]; subst; rewrite Ptrofs.add_zero; auto.   
   destruct v1; try discriminate; try constructor;
   destruct v2; try discriminate; destruct Archi.ptr64; try discriminate; inv H1; auto; try constructor.
   destruct (eq_block b b0); try discriminate.
   destruct (proj_sumbool (zlt 0 (sizeof ty)) &&
       proj_sumbool (zle (sizeof ty) Ptrofs.max_signed)); try discriminate.
   inv H3. unfold Vptrofs. destruct (Archi.ptr64); simpl; auto.
1,2: inv H; econstructor; eauto;
   apply mem_lemmas.flatinj_E in H4; destruct H4 as [? [? ?]]; subst; rewrite Ptrofs.add_zero; auto.
   destruct (eq_block b b0); try discriminate.
   destruct (proj_sumbool (zlt 0 (sizeof ty)) &&
       proj_sumbool (zle (sizeof ty) Ptrofs.max_signed)); try discriminate.
   inv H3. unfold Vptrofs. destruct (Archi.ptr64); simpl; auto; constructor.
   destruct v1; try discriminate;
   destruct v2; try discriminate; destruct Archi.ptr64; try discriminate; inv H1; auto; try constructor.
1,2:   inv H; econstructor; eauto;
   apply mem_lemmas.flatinj_E in H4; destruct H4 as [? [? ?]]; subst; rewrite Ptrofs.add_zero; auto.
   unfold Cop.sem_binarith in H1.
   destruct (Cop.sem_cast v1 t1
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   destruct (Cop.sem_cast v2 t2
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   eapply sem_cast_wellformed in Heqo; eauto.
   eapply sem_cast_wellformed in Heqo0; eauto.
   destruct (Cop.classify_binarith t1 t2); try discriminate;
   try solve [destruct v0; inv H1; destruct v3; inv H3; constructor].
-
   unfold Cop.sem_shl, Cop.sem_shift in H1.
   destruct (Cop.classify_shift t1 t2); try discriminate;
   destruct v1; try discriminate; destruct v2; try discriminate;
   revert H1; simple_if_tac; intro H1; inv H1; constructor.
-
   unfold Cop.sem_shr, Cop.sem_shift in H1.
   destruct (Cop.classify_shift t1 t2); try discriminate;
   destruct v1; try discriminate; destruct v2; try discriminate;
   revert H1; simple_if_tac; intro H1; inv H1; constructor.
Qed.

Lemma cur_perm_maxedmem:
 forall m loc ofs p,
  Mem.perm m loc ofs Cur p -> Mem.perm (maxedmem m) loc ofs Cur p.
Admitted.

Lemma loadbytes_proj_wellformed:
  forall ge m loc ofs sz bl ch q,
  block_wellformed (Mem.nextblock m) loc ->
  mem_wellformed ge m ->
  Mem.loadbytes m loc ofs sz = Some bl ->
  val_wellformed (Mem.nextblock m) (Val.load_result ch (proj_value q bl)).
Proof.
intros.
assert (forall ch, val_wellformed (Mem.nextblock m) (Val.load_result ch Vundef)) 
 by (intros; destruct ch0; simpl; hnf; auto).
unfold proj_value.
destruct bl; auto.
destruct m0; auto.
destruct (check_value (size_quantity_nat q) v q (Fragment v q0 n :: bl)) eqn:?H; auto.
assert (val_wellformed (Mem.nextblock m) v). {
 clear - H1 H H0.
 apply mem_lemmas.loadbytes_D in H1.
 destruct H1.
 destruct (zle sz 0).
 replace (Z.to_nat sz) with O in H2.
 inv H2.
 clear - l. symmetry; apply Z_to_nat_neg; auto.
 simpl in H2.
 inv H2.
 destruct H0.
 red.
 destruct (Z.to_nat sz) eqn:?H. inv H4. inv H4.
 hnf in H0.
  inv H0. clear mi_perm mi_align.
  specialize (mi_memval loc ofs loc 0).
  simpl Mem.mem_contents in mi_memval.
  rewrite Z.add_0_r in mi_memval.
  rewrite <- H6 in mi_memval.
  spec mi_memval. apply mem_lemmas.flatinj_I. apply H.
  spec mi_memval.
  specialize (H1 ofs).
  spec H1. omega.
  clear - H1.
  apply cur_perm_maxedmem; auto.
  inv mi_memval. auto.
}
  clear - H4.
  destruct ch,v; simpl; auto; constructor.
Qed.

Lemma deref_loc_wellformed: 
  forall ge m loc ofs t1 v,
  mem_wellformed ge m ->
  block_wellformed (Mem.nextblock m) loc ->
  deref_loc t1 m loc ofs v -> 
  val_wellformed (Mem.nextblock m) v.
Proof.
intros.
inv H1; auto.
unfold Mem.loadv in H3.
apply Mem.load_loadbytes in H3.
destruct H3 as [bl [? ?]].
subst.
unfold decode_val.
destruct (proj_bytes bl) eqn:?H.
destruct chunk; hnf; auto.
destruct chunk; try solve [hnf; auto].
1,2: destruct Archi.ptr64; try solve [hnf; auto].
all: try eapply loadbytes_proj_wellformed in H1; eauto.
hnf.
econstructor.
apply mem_lemmas.flatinj_I; auto.
rewrite Ptrofs.add_zero; auto.
econstructor.
apply mem_lemmas.flatinj_I; auto.
rewrite Ptrofs.add_zero; auto.
Qed.

Lemma sem_unary_operation_wellformed:
   forall ge m op t v1 v,
   mem_wellformed ge m ->
   val_wellformed (Mem.nextblock m) v1 ->
   Cop.sem_unary_operation op v1 t m = Some v ->
  val_wellformed (Mem.nextblock m) v.
Proof.
intros.
unfold Cop.sem_unary_operation in H1.
unfold Cop.sem_notbool, Cop.sem_notint, Cop.sem_neg, Cop.sem_absfloat in H1.
destruct op.
-
unfold option_map in H1.
destruct (Cop.bool_val v1 t0 m); inv H1.
destruct (negb b); constructor.
-
destruct (Cop.classify_notint t0); inv H1.
destruct v1; inv H3. constructor.
destruct v1; inv H3. constructor.
-
destruct (Cop.classify_neg t0); inv H1;
(destruct v1; inv H3; constructor).
-
destruct (Cop.classify_neg t0); inv H1;
(destruct v1; inv H3; constructor).
Qed.


Lemma eval_expr_wellformed:
  forall ge e le m a v,
  venv_wellformed (Mem.nextblock m) e ->
  tenv_wellformed (Mem.nextblock m) le ->
  mem_wellformed ge m ->
  eval_expr ge e le m a v ->
  val_wellformed (Mem.nextblock m) v
with eval_lvalue_wellformed: 
  forall ge e le m a b z,
  venv_wellformed (Mem.nextblock m) e ->
  tenv_wellformed (Mem.nextblock m) le ->
  mem_wellformed ge m ->
  eval_lvalue ge e le m a b z ->
  val_wellformed (Mem.nextblock m) (Vptr b z).
Proof.
-
clear eval_expr_wellformed.
intros.
induction H2; try constructor; eauto.
+ eapply sem_unary_operation_wellformed in H3; eauto.
+ eapply binary_operation_wellformed in H2; eauto.
+ eapply sem_cast_wellformed; try apply H3; auto.
+ apply eval_lvalue_wellformed in H2; auto.
   eapply deref_loc_wellformed in H3; eauto.
   clear - H2. inv H2.
   unfold Mem.flat_inj in H3. if_tac in H3; inv H3.  auto. 
-
clear eval_lvalue_wellformed.
intros.
induction H2; try constructor; eauto.
+
apply H in H2. simpl in H2.
red.
econstructor.
apply mem_lemmas.flatinj_I. apply H2.
rewrite Ptrofs.add_zero. auto.
+ econstructor.
instantiate (1:=0).
destruct H1.
apply Genv.genv_symb_range in H3.
unfold Mem.flat_inj.
rewrite if_true; auto.
eapply Plt_Ple_trans; eauto.
reflexivity.
+
eapply eval_expr_wellformed in H2; eauto.
inv H2.
econstructor; eauto.
unfold Mem.flat_inj in H9.
if_tac in H9; inv H9.
rewrite Ptrofs.add_assoc. f_equal.
rewrite Ptrofs.add_zero; auto.
Qed.

Lemma eval_exprlist_wellformed:
  forall ge e le m a tl vl,
  venv_wellformed (Mem.nextblock m) e ->
  tenv_wellformed (Mem.nextblock m) le ->
  mem_wellformed ge m ->
  eval_exprlist ge e le m a tl vl ->
  Forall (val_wellformed (Mem.nextblock m)) vl.
Proof.
intros.
induction H2; constructor; auto.
apply eval_expr_wellformed in H2; auto.
eapply sem_cast_wellformed in H3; eauto.
Qed.

Lemma find_label_wellformed:
 forall nextb lbl s s' (k : cont) (k' : cont),
  cont_wellformed nextb k ->
  find_label lbl s k = Some (s',k') ->
  cont_wellformed nextb k'
with find_label_ls_wellformed:
 forall nextb lbl s s' (k : cont) (k' : cont),
  cont_wellformed nextb k ->
  find_label_ls lbl s k = Some (s', k') ->
  cont_wellformed nextb k'.
Proof.
* clear find_label_wellformed.
induction s; simpl; intros; try discriminate.
-
destruct (find_label lbl s1
         (Kseq s2 k)) eqn:?; inv H0.
apply IHs1 in Heqo; auto.
repeat constructor; auto.
apply IHs2 in H2; auto.
-
destruct (find_label lbl s1 k) eqn:?; inv H0.
apply IHs1 in Heqo; auto.
apply IHs2 in H2; auto.
-
destruct (find_label lbl s1 (Kloop1 s1 s2 k)) eqn:?; inv H0.
apply IHs1 in Heqo; auto.
apply IHs2 in H2; auto.
-
eapply find_label_ls_wellformed in H0; eauto.
-
if_tac in H0.
subst. inv H0. auto.
apply IHs in H0; auto.
*
clear find_label_ls_wellformed.
induction s; intros.
inv H0.
simpl in H0.
destruct (find_label lbl s
         (Kseq (seq_of_labeled_statement s0) k)) eqn:?H; inv H0.
eapply find_label_wellformed; try apply H1; eauto.
repeat constructor; auto.
apply IHs in H3; auto.
Qed.

Lemma call_cont_wellformed_lemma:
  forall b k, 
    cont_wellformed b k -> cont_wellformed b (call_cont k).
Proof.
induction k; simpl; intros; auto.
Qed.

Lemma mem_wellformed_goto:
 forall f (k k' : cont) (lbl : Clight.label)
       (s' : Clight.statement) (nextb : block),
  cont_wellformed nextb k -> 
  find_label lbl (fn_body f) (call_cont k) = Some (s', k') ->
  cont_wellformed nextb k'.
Proof.
intros.
apply call_cont_wellformed_lemma in H.
forget (call_cont k) as k0. clear k; rename k0 into k.
revert H H0.
apply find_label_wellformed.
Qed.

Lemma storebytes_access_eq:
  forall m b z x m',
  Mem.storebytes m b z x = Some m' ->
  Mem.mem_access m = Mem.mem_access m'.
Admitted.

Lemma mem_access_eq_maxedmem:
 forall m m', 
   Mem.mem_access m = Mem.mem_access m' ->
  Mem.mem_access (maxedmem m') = Mem.mem_access (maxedmem m).
Admitted.

Lemma loadbytes_storebytes_wellformed:
   forall ge m b' z' sz b z bytes m',
   mem_wellformed ge m ->
   Mem.loadbytes m b' z' sz = Some bytes ->
   Mem.storebytes m b z bytes = Some m' -> 
   mem_wellformed ge m'.
Proof.
intros.
destruct H as [H H5].
pose proof (Mem.nextblock_storebytes _ _ _ _ _ H1).
split.
2: rewrite H2; auto.
red in H.
apply mem_lemmas.loadbytes_D in H0.
destruct H0.
subst bytes.
red.
assert (H3': forall ofs, 
     Mem.perm (maxedmem m) b' ofs Cur Readable ->
     memval_inject (Mem.flat_inj (Mem.nextblock m))
       (ZMap.get ofs (Mem.mem_contents m) !! b')
       (ZMap.get ofs (Mem.mem_contents m) !! b')).  {
 inv H. clear mi_perm mi_align.
 intros. specialize (mi_memval b' ofs b' 0).
 rewrite Z.add_0_r in mi_memval.
 apply mi_memval; auto.
 apply mem_lemmas.flatinj_I.
 hnf in H.
 destruct (plt b' (Mem.nextblock m)); auto. elimtype False.
 rewrite (Mem.nextblock_noaccess (maxedmem m) b' ofs Cur) in H.
 auto.
 simpl; auto.
}
assert (H3: forall ofs, 
     Mem.perm (maxedmem m) b ofs Cur Readable ->
     memval_inject (Mem.flat_inj (Mem.nextblock m))
       (ZMap.get ofs (Mem.mem_contents m) !! b)
       (ZMap.get ofs (Mem.mem_contents m) !! b)).  {
 inv H. clear mi_perm mi_align.
 intros. specialize (mi_memval b ofs b 0).
 rewrite Z.add_0_r in mi_memval.
 apply mi_memval; auto.
 apply mem_lemmas.flatinj_I.
 hnf in H.
 destruct (plt b (Mem.nextblock m)); auto. elimtype False.
 rewrite (Mem.nextblock_noaccess (maxedmem m) b ofs Cur) in H.
 auto.
 simpl; auto.
}
assert (H9: Mem.perm (maxedmem m') = Mem.perm (maxedmem m)). {
   clear - H1.
   unfold Mem.perm.
   extensionality b0 ofs k p.
   f_equal. f_equal.
   apply storebytes_access_eq in H1. clear - H1.
   apply mem_access_eq_maxedmem; auto.
}
generalize H; intro H'. 
inv H.
constructor.
-
clear mi_align mi_memval.
intros.
rewrite H2 in H.
specialize (mi_perm b1 b2 delta ofs k p H).
rewrite H9 in H4|-*.
auto.
-
intros.
apply (mi_align b1 b2 delta chunk ofs p).
rewrite H2 in H; auto.
red in H4|-*.
rewrite H9 in H4; auto.
-
intros.
apply mem_lemmas.flatinj_E in H.
destruct H as [? [? ?]]; subst.
rewrite Z.add_0_r.
simpl.
clear mi_perm mi_align mi_memval.
rewrite H2.
rewrite H2 in H7.
forget ((Mem.mem_contents m) !! b') as f.
assert (Forall (fun x => memval_inject (Mem.flat_inj (Mem.nextblock m))  x x) 
  (Mem.getN (Z.to_nat sz) z' f)). {
 clear H1.
 destruct (zlt sz 0). rewrite Z_to_nat_neg by omega. constructor.
 rewrite <- (Z2Nat.id sz) in H0 by omega. forget (Z.to_nat sz) as n. 
 clear sz g.
 revert z' H0; induction n; intros. simpl. constructor.
 rewrite inj_S in H0.
 simpl Mem.getN.
 constructor.
 2:{ apply IHn. hnf; intros. apply H0. omega. }
 clear IHn.
 apply H3'.
 apply cur_perm_maxedmem.
 apply H0.
 omega.
}
forget (Mem.getN (Z.to_nat sz) z' f) as bytes.
apply Mem.storebytes_mem_contents in H1.
rewrite H1. clear H1.
destruct (eq_block b1 b);
  [subst b1; rewrite PMap.gss  | rewrite PMap.gso by auto].
+
forget ((Mem.mem_contents m) !! b) as g.
rewrite H9 in H4.
clear - H H3 H4.
revert z g H3.
induction bytes; intros.
simpl. apply H3; auto.
simpl.
inv H.
apply IHbytes; auto.
intros.
destruct (zeq ofs0 z).
subst.
rewrite ZMap.gss; auto.
rewrite ZMap.gso; auto.
+
inv H'.
specialize (mi_memval b1 ofs b1 0).
rewrite Z.add_0_r in mi_memval.
apply mi_memval.
 apply mem_lemmas.flatinj_I.
auto.
rewrite H9 in H4; auto.
Qed.

Lemma mem_wellformed_freelist:
  forall ge m bl m', Mem.free_list m bl = Some m' -> 
  mem_wellformed ge m -> mem_wellformed ge m'.
Proof.
intros.
revert  bl m H H0; induction bl; simpl; intros.
inv H; auto.
destruct a as [[??]?].
destruct (Mem.free m b z z0) eqn:?H; inv H.
apply IHbl with m0; auto.
clear - H0 H1.
destruct H0.
pose proof (Mem.nextblock_free _ _ _ _ _ H1).
split; rewrite H2; auto.
eapply (mem_lemmas.free_neutral (Mem.nextblock m) (maxedmem m) z z0 b); auto.
clear - H1.
admit. (* OK *)
Admitted.


Lemma maxedmem_neutral':
  forall m
   (pm : access_map)
   (Hlt : permMapLt pm (getMaxPerm m)),
  Mem.inject_neutral (Mem.nextblock m) (maxedmem m) ->
  Mem.inject_neutral (Mem.nextblock m) (maxedmem (restrPermMap Hlt)).
Proof.
intros.
unfold Mem.inject_neutral in *.
inv H.
constructor; intros; simpl in *.
-
unfold Mem.flat_inj in H.
if_tac in H; inv H.
rewrite Z.add_0_r. auto.
-
eapply mi_align.
eassumption.
instantiate (1:=p); instantiate (1:=ofs).
clear - H0.
hnf; intros.
specialize (H0 _ H).
clear - H0.
admit. (* fine *)
Admitted.

Lemma alloc_variables_wellformed: 
  forall ge ve m vl ve' m',
   mem_wellformed ge m ->
   venv_wellformed (Mem.nextblock m) ve ->
   alloc_variables ge ve m vl ve' m' ->
   venv_wellformed (Mem.nextblock m') ve' /\ mem_wellformed ge m' /\ (Mem.nextblock m <= Mem.nextblock m')%positive.
Proof.
  intros.
  revert ve m H H0 H1; induction vl; simpl; intros.
  inv H1. split3; auto. apply Pos.le_refl.
  inv H1.
  apply IHvl in H9.
-
  destruct H9 as [? [? ?]].
  split3; auto.
  eapply Pos.le_trans; try apply H3.
  apply Mem.nextblock_alloc in H6. rewrite H6.
  apply Ple_succ.
-
  clear - H6 H.
  destruct H.
  split.
  eapply (Mem.alloc_inject_neutral (Mem.nextblock m1)) in H6.
  admit.
  admit.
  apply Mem.nextblock_alloc in H6. rewrite H6. apply Plt_succ.
  apply Mem.nextblock_alloc in H6. rewrite H6.
  eapply Ple_trans; try eassumption.
  apply Plt_Ple; apply Plt_succ.
-
  apply set_venv_wellformed.
  apply Mem.valid_new_block in H6. red in H6. apply H6.
  eapply alloc_venv_wellformed; try eassumption.
  apply Mem.nextblock_alloc in H6. rewrite H6.
  apply Ple_succ.
Admitted.

Lemma bind_parameter_temps_wellformed:
  forall m fl vl te te',
    tenv_wellformed (Mem.nextblock m) te ->
    Forall (val_wellformed (Mem.nextblock m))vl ->
    bind_parameter_temps fl vl te = Some te' ->
    tenv_wellformed (Mem.nextblock m) te'.
Proof.
induction fl; intros; auto.
inv H1. destruct vl; inv H3. auto.
inv H1.
destruct a.
destruct vl; inv H3.
inv H0.
apply IHfl in H2; auto.
apply set_tenv_wellformed; auto.
Qed.

Lemma inline_external_call_mem_wd: (* this whole lemma is probably obsolete *)
  forall (ge: genv) ef vargs m vres m',
  Events.external_call ef ge vargs m Events.E0 vres m' ->
  AST.ef_inline ef = true ->
  Forall (val_wellformed (Mem.nextblock m)) vargs ->
  Smallstep.globals_not_fresh ge m ->
  mem_wd2 m -> mem_wd2 m' /\
              val_wellformed (Mem.nextblock m') vres /\
              (Mem.nextblock m <= Mem.nextblock m')%positive.
Proof.
intros.
destruct ef; try solve [inv H0].
hnf in H.
assert (EFP := (Events.external_functions_properties name sg)).
pose proof (Events.ec_mem_inject' EFP).
specialize (H4 (Genv.to_senv ge)  (Genv.to_senv ge)
   vargs m Events.E0 vres m' (Mem.flat_inj (Mem.nextblock m))
   m vargs).
spec H4. {
 split; [|split3]; auto.
 intros.
 apply mem_lemmas.flatinj_E in H5.
  destruct H5 as [? [? ?]]; split; subst; auto.
 intros.
 exists b1; split; auto.
 unfold Mem.flat_inj. rewrite if_true; auto.
 clear - H2 H6. {
   red in H2. apply Senv.find_symbol_below in H6.
   eapply Plt_Ple_trans; eauto.
 }
 intros.
 apply mem_lemmas.flatinj_E in H5.
  destruct H5 as [? [? ?]]; subst; auto.
}
 specialize (H4 H).
 spec H4. {
   clear - H3.
  admit.  (* needs work *)(* but this whole lemma is probably obsolete *)
 }
 spec H4. {
   clear - H1. 
 admit.  (* looks OK *)(* but this whole lemma is probably obsolete *)
}
 destruct H4 as [f' [vres' [m2' [t' [? [? [? [? [? [? [? ?]]]]]]]]]]].
 assert (m2'=m'). {
   inv H11.
  eapply (Events.ec_determ EFP (Genv.to_senv ge) ); eauto.
}
 subst m2'.
 assert (Mem.inject (Mem.flat_inj (Mem.nextblock m')) m' m'). {
 clear - H6.
 admit. (* Santiago conjectures... *)(* but this whole lemma is probably obsolete *)
}
 split3; auto.
 clear - H12; admit.
{
 clear - H5 H6. hnf. destruct vres; auto.
  apply Val.inject_ptr with 0.
  apply mem_lemmas.flatinj_I; auto.
  pose proof (Mem.mi_freeblocks _ _ _ H6 b).
  unfold Mem.valid_block in H.
  destruct (plt b (Mem.nextblock m')); auto.
  apply H in n.
  inv H5. congruence.
  rewrite Ptrofs.add_zero; auto.
}
 eapply (Events.ec_valid_block EFP) with (b:=Pos.pred (Mem.nextblock m)) in H.
 clear - H.
 red in H. unfold Plt in H. admit.
 clear. red. admit.
-
inv H. inv H4.
split3; auto.
admit.  (* OK *)
apply Ple_refl.
-
inv H.
inv H4.
inv H1. inv H8. inv H9.
split3.
eapply mem_wd2_store in H5; eauto.
admit.
apply Mem.nextblock_store in H5. rewrite H5.
admit. (* but this whole lemma is probably obsolete *)
admit. (* but this whole lemma is probably obsolete *)
-
admit.  (* factor out extcall_properties from the first case above,
   and then use extcall_memcpy_ok *)(* but this whole lemma is probably obsolete *)
-
inv H.
-
inv H.
-
admit.  (* factor out extcall_properties from the first case above,
   and then use inline_assembly_properties *)
-
inv H.
split3; auto.
constructor.
apply Ple_refl.
Admitted. (* but this whole lemma is probably obsolete *)

Module Test.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Definition juicy_threads_wellformed ge m tp :=
   @threads_wellformed _ (@THE_JUICY_MACHINE.JSem ge) core_wellformed m tp.

Definition dry_threads_wellformed ge m tp :=
   @threads_wellformed _ (@ClightSemanticsForMachines.Clight_newSem ge) core_wellformed m tp.
End Test.


Lemma external_call_wellformed: 
  forall (ge: genv) ef vargs m vres m',
  Forall (val_wellformed (Mem.nextblock m)) vargs ->
  AST.ef_inline ef = true -> (* needed or not? *)
  ef_permitted ef = true -> (* needed or not? *)
  Events.external_call ef ge vargs m Events.E0 vres m' ->
  mem_wellformed ge m ->
 mem_wellformed ge m' /\
 val_wellformed (Mem.nextblock m') vres /\
 Ple (Mem.nextblock m) (Mem.nextblock m').
Admitted.

Lemma cl_step_wellformed:
  forall ge m c pm Hlt c' m',
      mem_wellformed ge m ->
      core_wellformed (Mem.nextblock m) c ->
      Clight_core.cl_step ge c (@restrPermMap pm m Hlt) c' m' ->
      mem_wellformed ge m' /\ 
      core_wellformed (Mem.nextblock m') c'.
Proof.
intros.
hnf in H1.
assert (mem_wellformed ge (restrPermMap Hlt)). {
  clear - Hlt H.
  hnf in H|-*. simpl.
  destruct H; split; auto.
  apply maxedmem_neutral'; auto.
}
change (Mem.nextblock m) with (Mem.nextblock (restrPermMap Hlt)) in *.
forget (restrPermMap Hlt) as m1.
clear m Hlt pm H.
rename m1 into m.
induction H1;
simpl in H0|-*;
try (destruct H0 as [Hv [Ht Hc]]);
try solve [split; [ | split3]; auto];
try (split; [ | split3]; auto; [idtac]).
- (* assign *)
replace (Mem.nextblock m') with (Mem.nextblock m).
2:{ inv H4. apply mem_lemmas.nextblock_storev in H5; auto.
    apply Mem.nextblock_storebytes in H9; auto.
}
split; [ | split3]; auto.
clear - H2 H4.
inv H4; destruct H2; split; auto.
clear - H0 H1.
unfold Mem.storev in H0.
admit.
apply Mem.nextblock_store in H0; rewrite H0; auto.
clear - H2 H6.
admit.
apply Mem.nextblock_storebytes in H6; rewrite H6; auto.
- (* set *)
eapply eval_expr_wellformed in H; eauto.
intros ? ? ?.
destruct (peq id i).
subst. rewrite PTree.gss in H0. inv H0; auto.
rewrite PTree.gso in H0 by auto.
apply Ht in H0; auto.
- (* call *)
eapply eval_exprlist_wellformed; eauto.
- (* builtin *)
apply eval_exprlist_wellformed in H3; auto.
destruct (external_call_wellformed ge ef vargs m vres m' H3 H H1 H4 H2)
  as [? [? ?]].
split3; auto.
eapply alloc_venv_wellformed; try eassumption.
split; auto.
destruct optid; simpl; auto.
eapply set_tenv_wellformed; eauto.
eapply alloc_tenv_wellformed; try eassumption.
eapply alloc_tenv_wellformed; try eassumption.
eapply alloc_cont_wellformed; try eassumption.
- (* return_0 *)
pose proof (mem_wellformed_freelist _ _ _ _ H H2).
split3; auto.
constructor.
apply call_cont_wellformed_lemma; auto.
apply mem_lemmas.nextblock_freelist in H.
rewrite H; auto.
- (* return_1 *)
pose proof (mem_wellformed_freelist _ _ _ _ H3 H2).
apply mem_lemmas.nextblock_freelist in H3.
rewrite H3.
split3; auto.
eapply eval_expr_wellformed in H; eauto.
eapply sem_cast_wellformed in H1; eauto.
apply call_cont_wellformed_lemma; auto.
- (* skip_call *)
pose proof (mem_wellformed_freelist _ _ _ _ H1 H2).
split3; auto.
constructor.
apply mem_lemmas.nextblock_freelist in H1.
rewrite H1; auto.
- (* step_goto *)
eapply find_label_wellformed in H; eauto.
apply call_cont_wellformed_lemma; auto.
- (* step_internal_function *)
inv H.
eapply alloc_variables_wellformed in H5; eauto.
2:{ unfold empty_env; hnf; intros. rewrite PTree.gempty in H. inv H. }
destruct H5 as [? [? ?]].
destruct H0.
eapply bind_parameter_temps_wellformed in H6; eauto.
split3; auto.
split.
eapply alloc_tenv_wellformed; eauto.
eapply alloc_cont_wellformed; eauto.
forget (Mem.nextblock m) as b.
clear.
induction (fn_temps f) as [|[??]]; simpl; intros.
hnf; intros. rewrite PTree.gempty in H; inv H.
hnf; intros.
destruct (peq i0 i).
subst i0. rewrite PTree.gss in H. inv H; constructor.
rewrite PTree.gso in H by auto. apply IHl in H. auto.
- (* step_external_function *)
destruct H0.
destruct (external_call_wellformed ge ef vargs m vres m' H0 H H1 H3 H2)
  as [? [? ?]].
split3; auto.
eapply alloc_cont_wellformed; try eassumption.
- (* step_returnstate *)
destruct Hc.
split3; auto.
split; auto.
destruct optid; simpl; auto.
apply set_tenv_wellformed; auto.
Admitted.

Lemma initial_core_wellformed:
  forall ge v args c m,
     Clight_core.cl_initial_core ge v args c ->
     Clight_core.arg_well_formed args m ->
     Smallstep.globals_not_fresh ge m ->
     core_wellformed (Mem.nextblock m) c.
Proof.
  (* Clight_self_simulation needs a weaker version of this, 
     where the initial state is injected (by any injection, not necessarily flat. *)
Admitted.

