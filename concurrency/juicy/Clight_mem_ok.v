Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_new.
Require Import VST.concurrency.juicy.mem_wd2.
(*
Require Import VST.concurrency.common.core_semantics.
Require Import VST.concurrency.common.bounded_maps.
Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.ClightSemanticsForMachines.
Require Import VST.concurrency.common.ClightMachine.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.juicy.semax_simlemmas.
Require Import VST.concurrency.juicy.semax_to_juicy_machine.
Require Import VST.concurrency.juicy.mem_wd2.
Require Import VST.veric.Clight_sim.
*)
Require Import VST.msl.eq_dec.
Require Import BinNums.
Require Import List. Import ListNotations.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "Strict Subproofs".


Section GE.
Variable ge: Clight.genv.

Section CTL_OK.
  Variable nextb : block.

Definition block_ok (b: block) := Plt b nextb.

Definition val_ok (v: val) : Prop := 
 match v with
 | Vptr b _ => block_ok b
 | _ => True
 end.

Definition venv_ok (ve: Clight.env) :=
  forall i bt, PTree.get i ve = Some bt -> block_ok (fst bt).

Definition tenv_ok (te: Clight.temp_env) :=
  forall i (v: val), PTree.get i te = Some v -> val_ok v.

Definition cont'_ok (k: Clight_new.cont') := 
 match k with
 | Clight_new.Kcall _ _ ve te => venv_ok ve /\ tenv_ok te
 | _ => True
 end.

Definition cont_ok (k: Clight_new.cont) := Forall cont'_ok k.

Definition corestate_ok (q: Clight_new.corestate) : Prop :=
 match q with
 | Clight_new.State ve te k => venv_ok ve /\ tenv_ok te /\ cont_ok k
 | Clight_new.ExtCall f vl _ ve te k => Forall val_ok vl /\ venv_ok ve /\ tenv_ok te /\ cont_ok k
 end.

End CTL_OK.



Section ALLOC_OK.
Variable nextb: positive.
Variable nextb': positive.
Variable LESS:  (nextb <= nextb')%positive.

Lemma alloc_block_ok: forall b, block_ok nextb b -> block_ok nextb' b.
Proof.
intros.
red in H|-*. eapply Pos.lt_le_trans; eauto.
Qed.

Lemma alloc_val_ok: forall v, val_ok nextb v -> val_ok nextb' v.
Proof.
intros; destruct v; auto.
red in H|-*. eapply alloc_block_ok; eauto.
Qed.

Lemma alloc_venv_ok: forall ve, venv_ok nextb ve -> venv_ok nextb' ve.
Proof.
intros.
red in H|-*; intros.
eapply alloc_block_ok; eauto.
Qed.

Lemma alloc_tenv_ok: forall te, tenv_ok nextb te -> tenv_ok nextb' te.
Proof.
intros.
red in H|-*; intros.
eapply alloc_val_ok; eauto.
Qed.

Lemma alloc_cont'_ok: forall k, cont'_ok nextb k -> cont'_ok nextb' k.
Proof.
destruct k; simpl; auto.
intros [? ?]; split.
eapply alloc_venv_ok; eauto.
eapply alloc_tenv_ok; eauto.
Qed.

Lemma alloc_cont_ok: forall k, cont_ok nextb k -> cont_ok nextb' k.
Proof.
intros.
red in H|-*.
revert H; apply Forall_impl.
apply alloc_cont'_ok.
Qed.

Lemma alloc_corestate_ok: forall q, corestate_ok nextb q -> corestate_ok nextb' q.
Proof.
destruct q; simpl.
intros [? [? ?]]; split; [|split].
eapply alloc_venv_ok; eauto.
eapply alloc_tenv_ok; eauto.
eapply alloc_cont_ok; eauto.
intros [? [? [? ?]]]; split; [|split; [|split]].
revert H; apply Forall_impl.
apply alloc_val_ok.
eapply alloc_venv_ok; eauto.
eapply alloc_tenv_ok; eauto.
eapply alloc_cont_ok; eauto.
Qed.

End ALLOC_OK.

Lemma set_tenv_ok:
  forall nextb i (v: val) te, val_ok nextb v -> tenv_ok nextb te ->
            tenv_ok nextb (PTree.set i v te).
Proof.
intros.
hnf in H0|-*.
intros.
destruct (eq_dec i i0).
subst. rewrite PTree.gss in H1. inv H1. auto.
rewrite PTree.gso in H1 by auto.
apply H0 in H1. auto.
Qed.

Lemma set_venv_ok:
  forall nextb i v ve, block_ok nextb (fst v) -> venv_ok nextb ve ->
            venv_ok nextb (PTree.set i v ve).
Proof.
intros.
hnf in H0|-*.
intros.
destruct (eq_dec i i0).
subst. rewrite PTree.gss in H1. inv H1. auto.
rewrite PTree.gso in H1 by auto.
apply H0 in H1. auto.
Qed.

Lemma sem_add_ptr_int_ok:
  forall nextb ty si v1 v2 v,
  val_ok nextb v1 ->
  val_ok nextb v2 ->
  Cop.sem_add_ptr_int (genv_cenv ge) ty si v1 v2 = Some v -> 
  val_ok nextb v.
Proof.
intros.
unfold Cop.sem_add_ptr_int in H1.
destruct v1; try discriminate;
destruct v2; try discriminate.
destruct Archi.ptr64; inv H1.  auto. 
inv H1; auto.
Qed.

Lemma sem_add_ptr_long_ok:
  forall nextb ty v1 v2 v,
  val_ok nextb v1 ->
  val_ok nextb v2 ->
  Cop.sem_add_ptr_long (genv_cenv ge) ty v1 v2 = Some v -> 
  val_ok nextb v.
Proof.
intros.
unfold Cop.sem_add_ptr_long in H1.
destruct v1; try discriminate;
destruct v2; try discriminate.
destruct Archi.ptr64; inv H1.  auto. 
inv H1; auto.
Qed.

Lemma sem_cast_ok:
  forall nextb v1 t1 t2 m v,
    val_ok nextb v1 ->
    Cop.sem_cast v1 t1 t2 m = Some v ->
     val_ok nextb v.
Proof.
intros.
unfold Cop.sem_cast in H0.
destruct (Cop.classify_cast t1 t2); try discriminate;
destruct v1; try discriminate;
try solve [inv H0; auto].
destruct (Cop.cast_float_int si2 f); inv H0; auto.
destruct (Cop.cast_single_int si2 f); inv H0; auto.
destruct (Cop.cast_float_long si2 f); inv H0; auto.
destruct (Cop.cast_single_long si2 f); inv H0; auto.
destruct Archi.ptr64; inv H0; auto.
destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); inv H2; auto.
hnf; auto.
if_tac in H0; inv H0; auto.
if_tac in H0; inv H0; auto.
Qed.

Lemma val_of_bool_ok:
  forall nextb b, val_ok nextb (Val.of_bool b).
Proof.
intros. destruct b; hnf; auto.
Qed.

Lemma sem_cmp_ok: 
  forall nextb op v1 t1 v2 t2 m v,
 Cop.sem_cmp op v1 t1 v2 t2 m = Some v ->
 val_ok nextb v1 -> val_ok nextb v2 -> val_ok nextb v.
Proof.
intros.
pose proof (val_of_bool_ok nextb).
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
eapply sem_cast_ok in Heqo; eauto.
eapply sem_cast_ok in Heqo0; eauto.
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

Lemma binary_operation_ok:
forall nextb (op : Cop.binary_operation) (v1 : val) (t1 : type) 
  (v2 : val) (t2 : type) (m : mem) (v : val),
  val_ok nextb v1 ->
  val_ok nextb v2 ->
  Cop.sem_binary_operation (Clight.genv_cenv ge) op v1 t1 v2 t2 m = Some v ->
  val_ok nextb v.
Proof.
intros.
 destruct op; simpl in *;
   try solve [revert H1 H H0; apply sem_cmp_ok];
try solve [
  match type of H1 with ?A _ _ _ _ _ = _ => unfold A in H1 end;
   unfold Cop.sem_binarith in H1;
   destruct (Cop.sem_cast v1 t1
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate;
   destruct (Cop.sem_cast v2 t2
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate;
   eapply sem_cast_ok in Heqo; eauto;
   eapply sem_cast_ok in Heqo0; eauto;
   destruct (Cop.classify_binarith t1 t2); try discriminate;
   try solve [destruct v0; inv H1; destruct v3; inv H3; auto];
   destruct v0; inv H1; destruct v3; inv H3; destruct s; inv H2;
   revert H3; simple_if_tac; intro H3; inv H3; auto].
- unfold Cop.sem_add in H1.
   destruct (Cop.classify_add t1 t2);
   try solve [eapply sem_add_ptr_int_ok; try eapply H1; eauto];
   try solve [eapply sem_add_ptr_long_ok; try eapply H1; eauto].
   unfold Cop.sem_binarith in H1.
   destruct (Cop.sem_cast v1 t1
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   destruct (Cop.sem_cast v2 t2
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   eapply sem_cast_ok in Heqo; eauto.
   eapply sem_cast_ok in Heqo0; eauto.
   destruct (Cop.classify_binarith t1 t2); try discriminate;
   try solve [destruct v0; inv H1; destruct v3; inv H3; auto].
- unfold Cop.sem_sub in H1.
   destruct (Cop.classify_sub t1 t2).
   destruct v1; try discriminate;
   destruct v2; try discriminate; destruct Archi.ptr64; try discriminate; inv H1; auto.
   destruct v1; try discriminate;
   destruct v2; try discriminate; destruct Archi.ptr64; try discriminate; inv H1; auto.
   destruct (eq_block b b0); try discriminate.
   destruct (proj_sumbool (zlt 0 (sizeof ty)) &&
       proj_sumbool (zle (sizeof ty) Ptrofs.max_signed)); try discriminate.
   inv H3. unfold Vptrofs. destruct (Archi.ptr64); simpl; auto.
   destruct (eq_block b b0); try discriminate.
   destruct (proj_sumbool (zlt 0 (sizeof ty)) &&
       proj_sumbool (zle (sizeof ty) Ptrofs.max_signed)); try discriminate.
   inv H3. unfold Vptrofs. destruct (Archi.ptr64); simpl; auto.
   destruct v1; try discriminate;
   destruct v2; try discriminate; destruct Archi.ptr64; try discriminate; inv H1; auto.
   unfold Cop.sem_binarith in H1.
   destruct (Cop.sem_cast v1 t1
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   destruct (Cop.sem_cast v2 t2
         (Cop.binarith_type (Cop.classify_binarith t1 t2)) m) eqn:?; try discriminate.
   eapply sem_cast_ok in Heqo; eauto.
   eapply sem_cast_ok in Heqo0; eauto.
   destruct (Cop.classify_binarith t1 t2); try discriminate;
   try solve [destruct v0; inv H1; destruct v3; inv H3; auto].
-
   unfold Cop.sem_shl, Cop.sem_shift in H1.
   destruct (Cop.classify_shift t1 t2); try discriminate;
   destruct v1; try discriminate; destruct v2; try discriminate;
   revert H1; simple_if_tac; intro H1; inv H1; auto.
-
   unfold Cop.sem_shr, Cop.sem_shift in H1.
   destruct (Cop.classify_shift t1 t2); try discriminate;
   destruct v1; try discriminate; destruct v2; try discriminate;
   revert H1; simple_if_tac; intro H1; inv H1; auto.
Qed.

Lemma loadbytes_proj_ok:
  forall m loc ofs sz bl ch q,
  block_ok (Mem.nextblock m) loc ->
  mem_wd2 m ->
  Mem.loadbytes m loc ofs sz = Some bl ->
  val_ok (Mem.nextblock m) (Val.load_result ch (proj_value q bl)).
Proof.
intros.
assert (forall ch, val_ok (Mem.nextblock m) (Val.load_result ch Vundef)) 
 by (intros; destruct ch0; simpl; hnf; auto).
unfold proj_value.
destruct bl; auto.
destruct m0; auto.
destruct (check_value (size_quantity_nat q) v q (Fragment v q0 n :: bl)) eqn:?H; auto.
assert (val_ok (Mem.nextblock m) v). {
 clear - H1 H H0.
 red in H0.
 specialize (H0 loc ofs).
 apply mem_lemmas.loadbytes_D in H1.
 destruct H1.
 destruct (nat_of_Z sz).
 inv H2.
 simpl in H2.
 inv H2.
 rewrite <- H4 in H0.
 inv H0.
 inv H3; try solve [hnf; auto].
 unfold Mem.flat_inj in H6.
 if_tac in H6; inv H6.
 simpl.
 apply H0.
}
unfold Val.load_result.
destruct ch; try solve [hnf; auto];
destruct v; try solve [hnf; auto].
destruct Archi.ptr64; auto.
hnf; auto.
Qed.

Lemma deref_loc_ok: 
  forall m loc ofs t1 v,
  mem_wd2 m ->
  block_ok (Mem.nextblock m) loc ->
  deref_loc t1 m loc ofs v -> 
  val_ok (Mem.nextblock m) v.
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
all: eapply loadbytes_proj_ok; eauto.
Qed.

Lemma eval_expr_ok:
  forall (m : mem) (ve : Clight.env) (te : Clight.temp_env)
  (a : Clight.expr) (v : val),
@Smallstep.globals_not_fresh Clight.fundef type (Clight.genv_genv ge) m ->
mem_wd2 m ->
venv_ok (Mem.nextblock m) ve ->
tenv_ok (Mem.nextblock m) te ->
eval_expr ge ve te m a v -> 
val_ok (Mem.nextblock m) v
 with eval_lvalue_ok:
  forall (m : mem) (ve : Clight.env) (te : Clight.temp_env)
  (a : Clight.expr) (v : block) ofs,
@Smallstep.globals_not_fresh Clight.fundef type (Clight.genv_genv ge) m ->
mem_wd2 m ->
venv_ok (Mem.nextblock m) ve ->
tenv_ok (Mem.nextblock m) te ->
eval_lvalue ge ve te m a v ofs -> 
block_ok (Mem.nextblock m) v.
Proof.
* clear eval_expr_ok.
intros.
assert (Hof_bool: forall v, val_ok (Mem.nextblock m) (Val.of_bool v))
    by (intro v'; destruct v'; apply I).
induction H3; try solve [apply I].
 + apply H2 in H3; auto.
 + apply eval_lvalue_ok in H3; auto.
 + destruct op; simpl in H4. 
     - clear - Hof_bool H4 IHeval_expr.
        unfold Cop.sem_notbool, Cop.bool_val in H4. 
        destruct (Clight.typeof a) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
        simpl in H4; try discriminate;
        try match type of H4 with context [Archi.ptr64] => 
                          destruct Archi.ptr64; simpl in H4; try discriminate end;
        try (destruct v1; inv H4; auto;
           destruct Archi.ptr64; inv H0;
           destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); inv H1;
           apply I).
    - clear - Hof_bool H4 IHeval_expr.
        unfold Cop.sem_notint, Cop.bool_val in H4. 
        destruct (Clight.typeof a) as [ | [| | | ] [| ]| | [ | ] |  | | | | ];
        simpl in H4; try discriminate;
        try match type of H4 with context [Archi.ptr64] => 
                          destruct Archi.ptr64; simpl in H4; try discriminate end;
        try (destruct v1; inv H4; auto;
           destruct Archi.ptr64; inv H0;
           destruct (Mem.weak_valid_pointer m b (Ptrofs.unsigned i)); inv H1;
           apply I).
    - unfold Cop.sem_neg in H4.
        destruct (Cop.classify_neg (Clight.typeof a)); inv H4;
        destruct v1; inv H6; auto.
   - unfold Cop.sem_absfloat in H4.
        destruct (Cop.classify_neg (Clight.typeof a)); inv H4;
        destruct v1; inv H6; auto.
 + eapply binary_operation_ok; try apply H3; eauto.
 + eapply sem_cast_ok; try apply H4; eauto.
 + apply eval_lvalue_ok in H3; auto.
     eapply deref_loc_ok; try apply H4; auto.
* clear eval_lvalue_ok.
  intros.
  induction H3.
  apply H1 in H3. auto.
  clear - H H4.
  red in H.
  red. apply Genv.genv_symb_range in H4.
  eapply Pos.lt_le_trans; eauto.
  apply eval_expr_ok in H3; auto.
  apply eval_expr_ok in H3; auto.
  apply eval_expr_ok in H3; auto.
Qed.

Lemma eval_exprlist_ok:
  forall (m : mem) (ve : Clight.env) (te : Clight.temp_env)
  (al : list Clight.expr) tl (vl : list val),
@Smallstep.globals_not_fresh Clight.fundef type (Clight.genv_genv ge) m ->
mem_wd2 m ->
venv_ok (Mem.nextblock m) ve ->
tenv_ok (Mem.nextblock m) te ->
eval_exprlist ge ve te m al tl vl -> 
Forall (val_ok (Mem.nextblock m)) vl.
Proof.
intros.
induction H3.
constructor.
eapply eval_expr_ok in H3; eauto.
constructor; auto.
eapply sem_cast_ok in H4; eauto.
Qed.

Lemma find_label_ok:
 forall nextb lbl s (al : list cont') (k' : cont),
  cont_ok nextb al ->
  find_label lbl s al = Some k' ->
  cont_ok nextb k'
with find_label_ls_ok:
 forall nextb lbl s (al : list cont') (k' : cont),
  cont_ok nextb al ->
  find_label_ls lbl s al = Some k' ->
  cont_ok nextb k'.
Proof.
* clear find_label_ok.
induction s; simpl; intros; try discriminate.
-
destruct (find_label lbl s1
         (Kseq s2 :: al)) eqn:?; inv H0.
apply IHs1 in Heqo; auto.
repeat constructor; auto.
apply IHs2 in H2; auto.
-
destruct (find_label lbl s1 al) eqn:?; inv H0.
apply IHs1 in Heqo; auto.
apply IHs2 in H2; auto.
-
destruct (Kseq Scontinue :: Kloop1 s1 s2 :: al) eqn:?; inv H0.
destruct (find_label lbl s1 []) eqn:?; inv H2.
simpl in Heql. inv Heql.
apply IHs2 in H1; auto.
repeat constructor; auto.
simpl in Heql. inv Heql.
destruct  (Kseq Scontinue :: Kloop1 s1 s2 :: al) eqn:?; inv H2.
simpl in Heql; inv Heql.
simpl in Heql; inv Heql.
destruct (find_label lbl s1
         (Kseq Scontinue :: Kloop1 s1 s2 :: al)) eqn:?; inv H1.
apply IHs1 in Heqo; auto.
repeat constructor; auto.
apply IHs2 in H2; auto.
repeat constructor; auto.
- 
 eapply find_label_ls_ok; try apply H0; eauto.
 repeat constructor; auto.
-
 if_tac in H0. subst. inv H0. constructor; auto. constructor; auto.
 apply IHs in H0; auto.
* clear find_label_ls_ok.
induction s; intros.
inv H0.
simpl in H0.
destruct (find_label lbl s
         (Kseq (seq_of_labeled_statement s0) :: al)) eqn:?H; inv H0.
eapply find_label_ok; try apply H1; eauto.
repeat constructor; auto.
apply IHs in H3; auto.
Qed.

Lemma mem_ok_goto:
 forall (k : cont) (lbl : Clight.label)
       (s' : Clight.statement) (nextb : block),
   cont_ok nextb k ->
   forall (s : Clight.statement) (k' : cont),
   find_label lbl s
     (Kseq s' :: Clight_new.call_cont k) = 
    Some k' -> cont_ok nextb k'.
Proof.
intros.
change (Clight_new.Kseq s' :: Clight_new.call_cont k) with
  ([Clight_new.Kseq s'] ++ Clight_new.call_cont k) in H0.
assert (Forall (cont'_ok nextb) [Clight_new.Kseq s'] ).
repeat constructor.
remember [Clight_new.Kseq s'] as al.
clear Heqal.
eapply find_label_ok; try apply H0.
red.
apply sublist.Forall_app.
split; auto.
red in H.
clear - H.
induction k.
constructor.
inv H.
destruct a; simpl; auto.
Qed.

Lemma loadbytes_storebytes_wd2:
   forall m b' z' sz b z bytes m',
   mem_wd2 m ->
   Mem.loadbytes m b' z' sz = Some bytes ->
   Mem.storebytes m b z bytes = Some m' -> mem_wd2 m'.
Proof.
intros.
red in H.
apply mem_lemmas.loadbytes_D in H0.
destruct H0.
subst bytes.
generalize (H b'); intro.
forget ((Mem.mem_contents m) !! b') as f.
assert (Forall (fun x => memval_inject (Mem.flat_inj (Mem.nextblock m))  x x) 
  (Mem.getN (nat_of_Z sz) z' f)).
clear H0 H1. revert z'.
induction (nat_of_Z sz); intros. simpl. constructor.
constructor. auto. auto.
forget (Mem.getN (nat_of_Z sz) z' f) as bytes.
generalize (H b); intro.
red.
rewrite (Mem.nextblock_storebytes _ _ _ _ _ H1).
apply Mem.storebytes_mem_contents in H1.
rewrite H1. clear H1.
intros.
destruct (eq_block b0 b);
  [  | rewrite PMap.gso by auto; apply H].
subst.
rewrite PMap.gss.
forget ((Mem.mem_contents m) !! b) as g.
clear - H4 H3.
revert g H4.
revert z H3; induction bytes; intros.
simpl. auto.
inv H3.
simpl.
apply IHbytes; auto.
intros.
destruct (zeq ofs0 z).
subst.
rewrite ZMap.gss; auto.
rewrite ZMap.gso; auto.
Qed.

Lemma mem_wd_freelist:
  forall m bl m', Mem.free_list m bl = Some m' -> mem_wd2 m -> mem_wd2 m'.
Proof.
intros.
revert  bl m H H0; induction bl; simpl; intros.
inv H; auto.
destruct a as [[??]?].
destruct (Mem.free m b z z0) eqn:?H; inv H.
apply IHbl with m0; auto.
clear - H0 H1.
hnf; intros.
Transparent Mem.free.
destruct (eq_block b0 b).
subst b0.
unfold Mem.free in H1.
if_tac in H1.
inv H1.
simpl.
apply H0.
inv H1.
unfold Mem.free in H1.
if_tac in H1.
inv H1.
simpl.
apply H0.
inv H1.
Opaque Mem.free.
Qed.

Lemma alloc_variables_ok: 
  forall ve m vl ve' m',
   mem_wd2 m ->
   venv_ok (Mem.nextblock m) ve ->
   alloc_variables ge ve m vl ve' m' ->
   venv_ok (Mem.nextblock m') ve' /\ mem_wd2 m' /\ (Mem.nextblock m <= Mem.nextblock m')%positive.
Proof.
  intros.
  revert ve m H H0 H1; induction vl; simpl; intros.
  inv H1. split3; auto. apply Pos.le_refl.
  inv H1.
  apply IHvl in H9.
  destruct H9 as [? [? ?]].
  split3; auto.
  eapply Pos.le_trans; try apply H3.
  apply Mem.nextblock_alloc in H6. rewrite H6.
  apply Ple_succ.
  eapply mem_wd2_alloc; eauto.
  apply set_venv_ok.
  apply Mem.valid_new_block in H6. red in H6. apply H6.
  eapply alloc_venv_ok; try eassumption.
  apply Mem.nextblock_alloc in H6. rewrite H6.
  apply Ple_succ.
Qed.

Lemma bind_parameter_temps_ok:
  forall m fl vl te te',
    tenv_ok (Mem.nextblock m) te ->
    Forall (val_ok (Mem.nextblock m))vl ->
    bind_parameter_temps fl vl te = Some te' ->
    tenv_ok (Mem.nextblock m) te'.
Proof.
induction fl; intros; auto.
inv H1. destruct vl; inv H3. auto.
inv H1.
destruct a.
destruct vl; inv H3.
inv H0.
apply IHfl in H2; auto.
apply set_tenv_ok; auto.
Qed.

Lemma call_cont_ok_lemma:
 forall f optid k m ve' te' k',
call_cont k = Kcall optid f ve' te' :: k' ->
Forall (cont'_ok (Mem.nextblock m)) k ->
venv_ok (Mem.nextblock m) ve' /\
tenv_ok (Mem.nextblock m) te' /\ cont_ok (Mem.nextblock m) k'.
Proof.
intros.
revert H; induction k; simpl; intros. inv H.
inv H0.
destruct a; try solve [apply IHk in H; auto].
inv H.
inv H3. split3; auto.
Qed.

Lemma cl_step_ok:
  forall c m c' m',
Clight_new.cl_step ge c m c' m' ->
Smallstep.globals_not_fresh (Clight.genv_genv ge) m /\
mem_wd2 m /\ corestate_ok (Mem.nextblock m) c ->
mem_wd2 m' /\
corestate_ok (Mem.nextblock m') c' /\
(Mem.nextblock m <= Mem.nextblock m')%positive.
intros until m'. intro Hstep.
 induction Hstep; intros [? [? ?]]. 
* (* assign *)
  destruct H6 as [? [? Hk]].
  eapply eval_expr_ok in H1; eauto.
  eapply eval_lvalue_ok in H0; eauto.
  eapply sem_cast_ok in H2; eauto.
  assert (mem_wd.val_valid v m). {
   clear - H2.
    hnf. hnf in H2. destruct v; auto.
 }
  inv H3.
  unfold Mem.storev in H10.
  pose proof (mem_wd2_store _ _ _ _ _ _ H5 H10 H8).
  rewrite (Mem.nextblock_store _ _ _ _ _ _ H10).
  split3; auto.
  split3; auto. inv Hk; auto.
  apply Pos.le_refl.
  rewrite (Mem.nextblock_storebytes _ _ _ _ _ H14).
  split3.
  2: split3; auto; inv Hk; auto.
  2: apply Pos.le_refl.
  eapply loadbytes_storebytes_wd2; eauto.
* (* set *)
   destruct H2 as [? [? ?]]. inv H4.
   repeat split;  auto.
   2: apply Pos.le_refl.
   apply set_tenv_ok; auto.
   eapply eval_expr_ok; eauto.
* (* call_internal *)
 destruct H9 as [? [? ?]]. inv H11. clear H14.
  eapply eval_expr_ok in H0; eauto.
  eapply eval_exprlist_ok in H1; eauto.
  eapply alloc_variables_ok in H5; eauto;
   [ | clear; hnf; intros; rewrite PTree.gempty in H; inv H].
  destruct H5 as [? [? ?]].
  eapply bind_parameter_temps_ok in H6; eauto.
  split3; auto.
  split3; auto.
  eapply alloc_tenv_ok; eauto.
  repeat constructor; auto.
  eapply alloc_venv_ok; eauto.
  eapply alloc_tenv_ok; eauto.
  clear - H12 H15.
  revert H15; apply Forall_impl.
  apply alloc_cont'_ok; auto.
  clear. induction (fn_temps f); simpl. intros ? ? ?. rewrite PTree.gempty in H. inv H. destruct a.
  apply set_tenv_ok; auto. hnf; auto.  
*  (* call_external *)
 destruct H5 as [? [? ?]]. inv H7. clear H10.
  eapply eval_expr_ok in H0; eauto.
  eapply eval_exprlist_ok in H1; eauto.
  split3; auto.
  2: apply Pos.le_refl.
  split3; auto.
* (* seq *)
  apply IHHstep. split; [|split]; auto.
  destruct H1 as [? [? ?]];  split; [|split]; auto.
  repeat constructor. inv H3; auto.
* (* skip *)
  apply IHHstep. split; [|split]; auto.
  simpl in H1. destruct H1 as [? [? ?]]. split; [|split]; auto. inv H3. auto.
* (* continue *)
  apply IHHstep. split; [|split]; auto.
  simpl in H1. destruct H1 as [? [? ?]]. split; [|split]; auto. inv H3.
  clear - H7.
  induction k. constructor.
  inv H7.
  specialize (IHk H2).
  destruct a; auto. simpl in *. repeat constructor. auto.
  repeat constructor. simpl in *. constructor.
* (* break *)
  apply IHHstep. split; [|split]; auto.
  simpl in H1. destruct H1 as [? [? ?]]. split; [|split]; auto. inv H3.
  clear - H7.
  induction k. constructor.
  inv H7.
  specialize (IHk H2).
  destruct a; auto. simpl in *. repeat constructor.
* (* ifthenelse *)
  split; auto.
  split.
   2: apply Pos.le_refl.
  destruct H3 as [? [? ?]]. split;[ |split]; auto.
  constructor. constructor. inv H5; auto.
* (* for *)
  split; auto.
  split.
   2: apply Pos.le_refl.
  destruct H1 as [? [? ?]]. split;[ |split]; auto.
  repeat constructor.
  inv H3. auto.
* (* loop2 *)
  split; auto.
  split.
   2: apply Pos.le_refl.
  destruct H1 as [? [? ?]]. split;[ |split]; auto.
  repeat constructor.
  inv H3. auto.
* (* return *)
  rewrite (mem_lemmas.nextblock_freelist _ _ _ H0).
  split3.
  eapply mem_wd_freelist; eassumption.
  2: apply Pos.le_refl.
  clear - H H3 H1 H2 H4 H5.
  destruct H5 as [? [? ?]].
  inv H6. clear H9.
  assert (val_ok (Mem.nextblock m) v'). {
    destruct optexp.
    destruct H1  as [? [? ?]]. eapply eval_expr_ok in H1; eauto.
    eapply sem_cast_ok in H6; eauto. subst; hnf; auto.
  }
  clear H1.
  assert (venv_ok (Mem.nextblock m) ve' /\ tenv_ok (Mem.nextblock m) te' /\ cont_ok (Mem.nextblock m) k'). {
   eapply call_cont_ok_lemma; eauto.
  }
  destruct H1 as [? [? ?]].
  split3; auto.
  clear - H7 H2 H6.
  destruct optid; destruct H2; subst; auto.
  apply set_tenv_ok; auto.
* (* switch *)
  destruct H3 as [? [? ?]].
  split3; auto.
  2: apply Pos.le_refl.
  split3; auto. inv H5. constructor; auto.
* (* label *)
  apply IHHstep. split; [|split]; auto.
  simpl in H1. destruct H1 as [? [? ?]]. split; [|split]; auto. inv H3.
  constructor; auto.
* (* goto *)
  split; auto.
  split.
   2: apply Pos.le_refl.
  destruct H2 as [? [? ?]]. split; [|split]; auto.
  inv H4.
  eapply mem_ok_goto; eauto.
Qed.

End GE.
