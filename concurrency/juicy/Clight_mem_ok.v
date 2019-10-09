Require Import compcert.lib.Integers.
Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.common.Values.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Clight.
Require Import VST.sepcomp.event_semantics.
Require Import VST.veric.Clight_core.
Require Import VST.concurrency.juicy.mem_wd2.
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

Fixpoint cont_ok (k: cont) := 
 match k with
 | Kstop => True
 | Kseq _ k' => cont_ok k'
 | Kloop1 _ _ k' => cont_ok k'
 | Kloop2 _ _ k' => cont_ok k'
 | Kswitch k' => cont_ok k'
 | Kcall _ _ ve te k' => venv_ok ve /\ tenv_ok te /\ cont_ok k'
 end.

Definition corestate_ok (q: Clight_core.state) : Prop :=
 match q with
 | Clight_core.State _ _ k ve te => venv_ok ve /\ tenv_ok te /\ cont_ok k
 | Clight_core.Callstate f args k =>
       Forall val_ok args /\  cont_ok k
 | Clight_core.Returnstate v k => val_ok v /\ cont_ok k
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

(*
Lemma alloc_cont'_ok: forall k, cont'_ok nextb k -> cont'_ok nextb' k.
Proof.
destruct k; simpl; auto.
intros [? ?]; split.
eapply alloc_venv_ok; eauto.
eapply alloc_tenv_ok; eauto.
Qed.
*)

Lemma alloc_cont_ok: forall k, cont_ok nextb k -> cont_ok nextb' k.
Proof.
induction k; simpl; intros; auto.
destruct H as [? [? ?]]. split3; auto.
eapply alloc_venv_ok; eauto.
eapply alloc_tenv_ok; eauto.
Qed.

Lemma alloc_corestate_ok: forall q, corestate_ok nextb q -> corestate_ok nextb' q.
Proof.
destruct q; simpl.
intros [? [? ?]]; split; [|split].
eapply alloc_venv_ok; eauto.
eapply alloc_tenv_ok; eauto.
eapply alloc_cont_ok; eauto.
intros [? ?]; split.
eapply Forall_impl; try eassumption. apply alloc_val_ok.
apply alloc_cont_ok; auto.
intros [? ?]; split.
eapply alloc_val_ok; eauto.
apply alloc_cont_ok; auto.
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
 destruct (Z.to_nat sz).
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
 forall nextb lbl s s' (k : cont) (k' : cont),
  cont_ok nextb k ->
  find_label lbl s k = Some (s',k') ->
  cont_ok nextb k'
with find_label_ls_ok:
 forall nextb lbl s s' (k : cont) (k' : cont),
  cont_ok nextb k ->
  find_label_ls lbl s k = Some (s', k') ->
  cont_ok nextb k'.
Proof.
* clear find_label_ok.
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
eapply find_label_ls_ok in H0; eauto.
-
if_tac in H0.
subst. inv H0. auto.
apply IHs in H0; auto.
*
clear find_label_ls_ok.
induction s; intros.
inv H0.
simpl in H0.
destruct (find_label lbl s
         (Kseq (seq_of_labeled_statement s0) k)) eqn:?H; inv H0.
eapply find_label_ok; try apply H1; eauto.
repeat constructor; auto.
apply IHs in H3; auto.
Qed.

Lemma call_cont_ok_lemma:
  forall b k, 
    cont_ok b k -> cont_ok b (call_cont k).
Proof.
induction k; simpl; intros; auto.
Qed.

Lemma mem_ok_goto:
 forall f (k k' : cont) (lbl : Clight.label)
       (s' : Clight.statement) (nextb : block),
  cont_ok nextb k -> 
  find_label lbl (fn_body f) (call_cont k) = Some (s', k') ->
  cont_ok nextb k'.
Proof.
intros.
apply call_cont_ok_lemma in H.
forget (call_cont k) as k0. clear k; rename k0 into k.
revert H H0.
apply find_label_ok.
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
  (Mem.getN (Z.to_nat sz) z' f)).
clear H0 H1. revert z'.
induction (Z.to_nat sz); intros. simpl. constructor.
constructor. auto. auto.
forget (Mem.getN (Z.to_nat sz) z' f) as bytes.
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

End GE.

Lemma inline_external_call_mem_wd:
  forall (ge: genv) ef vargs m t vres m',
  Events.external_call ef ge vargs m t vres m' ->
  AST.ef_inline ef = true ->
  Forall (val_ok (Mem.nextblock m)) vargs ->
  Smallstep.globals_not_fresh ge m ->
  mem_wd2 m ->
  mem_wd2 m' /\ val_ok (Mem.nextblock m') vres /\ (Mem.nextblock m <= Mem.nextblock m')%positive.
Admitted.

Lemma cl_step_ok:
  forall (ge: genv) c m c' m',
 cl_step ge c m c' m' ->
Smallstep.globals_not_fresh (Clight.genv_genv ge) m /\
mem_wd2 m /\ corestate_ok (Mem.nextblock m) c ->
mem_wd2 m' /\
corestate_ok (Mem.nextblock m') c' /\
(Mem.nextblock m <= Mem.nextblock m')%positive.
Proof.
intros until m'. intro Hstep.
 induction Hstep; intros [? [? ?]];
  try (split3; [solve [auto] | solve [auto] | try apply Pos.le_refl]). 
* (* assign *)
  destruct H5 as [? [? Hk]].
  eapply eval_expr_ok in H0; eauto.
  eapply eval_lvalue_ok in H; eauto.
  eapply sem_cast_ok in H1; eauto.
  assert (mem_wd.val_valid v m). {
   clear - H1.
    hnf. hnf in H1. destruct v; auto.
 }
  inv H2.
  unfold Mem.storev in H9.
  pose proof (mem_wd2_store _ _ _ _ _ _ H4 H9 H7).
  rewrite (Mem.nextblock_store _ _ _ _ _ _ H9).
  split3; auto.
  split3; auto.
  apply Pos.le_refl.
  rewrite (Mem.nextblock_storebytes _ _ _ _ _ H13).
  split3.
  2: split3; auto; inv Hk; auto.
  2: apply Pos.le_refl.
  eapply loadbytes_storebytes_wd2; eauto.
* (* set *)
   destruct H2 as [? [? ?]].
   repeat split;  auto.
   2: apply Pos.le_refl.
   apply set_tenv_ok; auto.
   eapply eval_expr_ok; eauto.
*  destruct H6 as [? [? ?]].
  eapply eval_expr_ok in H0; try eassumption. (* *)
  eapply eval_exprlist_ok in H1; eauto.
  split3; auto.
  split3; auto.
  apply Pos.le_refl.
* (* builtin *)
  destruct H4 as [? [? ?]].
  eapply eval_exprlist_ok in H0; eauto.
  exploit inline_external_call_mem_wd; eauto.
  intros [? [? ?]].
  split3; auto. split3; auto.
  eapply alloc_venv_ok; eauto.
  destruct optid; auto.
  apply set_tenv_ok; auto.
  eapply alloc_tenv_ok; eauto.
  eapply alloc_tenv_ok; eauto.
  eapply alloc_cont_ok; eauto.
* (* return None *)
  rewrite (mem_lemmas.nextblock_freelist _ _ _ H).
  split3.
  eapply mem_wd_freelist; eassumption.
  destruct H2 as [? [? ?]].
  split. hnf; auto.
  apply call_cont_ok_lemma; auto.
  apply Pos.le_refl.
* (* return Some *)
  rewrite (mem_lemmas.nextblock_freelist _ _ _ H1).
  split3.
  eapply mem_wd_freelist; eassumption.
  destruct H4 as [? [? ?]]. hnf.
  split.
  eapply eval_expr_ok in H; eauto.
  eapply sem_cast_ok; eauto.
  apply call_cont_ok_lemma; auto.
  apply Pos.le_refl.
* (* return fall-through *)
  rewrite (mem_lemmas.nextblock_freelist _ _ _ H0).
  split3.
  eapply mem_wd_freelist; eassumption.
  simpl. destruct H3 as [? [? ?]]. auto.
  apply Pos.le_refl.
* (* goto *)
  split; auto.
  split; [ | apply Pos.le_refl].
  destruct H2 as [? [? ?]]. split; [|split]; auto.
  inv H.
  eapply mem_ok_goto; eauto.
* (* call_internal *)
  destruct H2 as [H2' H2].
  inv H.
  eapply alloc_variables_ok in H6; eauto;
   [ | clear; hnf; intros; rewrite PTree.gempty in H; inv H].
  destruct H6 as [? [? ?]].
  eapply bind_parameter_temps_ok in H7; eauto.
  split3; auto.
  split3; auto.
  eapply alloc_tenv_ok; eauto.
  eapply alloc_cont_ok; eauto.
  eapply alloc_tenv_ok; eauto.
  clear. induction (fn_temps f); simpl. intros ? ? ?. rewrite PTree.gempty in H. inv H. destruct a.
  apply set_tenv_ok; auto. hnf; auto.
* (* call_external inline *)
  destruct H3 as [? ?].
  exploit inline_external_call_mem_wd; eauto.
  intros [? [? ?]]; split3; auto.
  split; auto.
  eapply alloc_cont_ok; eauto.
* (* returnstate *)
  destruct H1.
  split3; auto.
  destruct H2 as [? [? ?]].
  split3; auto.
  destruct optid; auto.
  apply set_tenv_ok; auto. 
  apply Pos.le_refl.
Qed.
