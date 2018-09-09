Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_pred_lemmas.

Local Open Scope logic.

(******************************************

Basic lemmas about local_facts, isptr, offset_zero

******************************************)

Lemma local_facts_isptr: forall P Q (p: val), P p |-- !! Q -> (Q -> isptr p) -> P p = !! (isptr p) && P p.
Proof.
  intros.
  rewrite andp_comm; apply add_andp.
  eapply derives_trans; [eassumption |].
  apply prop_derives; auto.
Qed.

Lemma local_facts_offset_zero: forall P, (forall p, P p |-- !! isptr p) -> (forall p, P p = P (offset_val 0 p)).
Proof.
  intros.
  pose proof (H p).
  pose proof (H Vundef).
  destruct p; simpl in *; apply pred_ext; normalize.
all: try solve [eapply derives_trans; [eassumption | normalize]].
Qed.

(******************************************

Lemmas about mapsto and mapsto_.

******************************************)

Lemma mapsto_local_facts:
  forall sh t v1 v2,  mapsto sh t v1 v2 |-- !! (isptr v1 /\ tc_val' t v2).
Proof.
  intros.
  rewrite prop_and.
  apply andp_right.
  + unfold mapsto.
    destruct (access_mode t); try apply FF_left.
    destruct (type_is_volatile t); try apply FF_left.
    destruct v1; try apply FF_left.
    apply prop_right; split; auto; apply Coq.Init.Logic.I.
  + apply mapsto_tc_val'.
Qed.

Lemma mapsto__local_facts:
  forall sh t v1, mapsto_ sh t v1 |-- !! isptr v1.
Proof.
  intros.
  eapply derives_trans; [apply mapsto_local_facts |].
  apply prop_derives; tauto.
Qed.
Hint Resolve mapsto_local_facts mapsto__local_facts : saturate_local.

Lemma mapsto_offset_zero:
  forall sh t v1 v2, mapsto sh t v1 v2 = mapsto sh t (offset_val 0 v1) v2.
Proof.
  intros.
  change (mapsto sh t (offset_val 0 v1) v2) with ((fun v0 => mapsto sh t v0 v2) (offset_val 0 v1)).
  rewrite <- local_facts_offset_zero.
  reflexivity.
  intros.
  eapply derives_trans; [  apply mapsto_local_facts | ].
  normalize.
Qed.

Lemma mapsto__offset_zero:
  forall sh t v1, mapsto_ sh t v1 = mapsto_ sh t (offset_val 0 v1).
Proof.
  unfold mapsto_.
  intros.
  apply mapsto_offset_zero.
Qed.

Lemma mapsto_isptr: forall sh t v1 v2, mapsto sh t v1 v2 = !! (isptr v1) && mapsto sh t v1 v2.
Proof.
  intros.
  change (mapsto sh t v1 v2) with ((fun v1 => mapsto sh t v1 v2) v1).
  eapply local_facts_isptr.
  + apply mapsto_local_facts.
  + tauto.
Qed.

Lemma mapsto__isptr: forall sh t v1, mapsto_ sh t v1 = !! (isptr v1) && mapsto_ sh t v1.
Proof.
  intros.
  eapply local_facts_isptr.
  + apply mapsto_local_facts.
  + tauto.
Qed.

(******************************************

Lemmas about memory_block

******************************************)

Hint Rewrite memory_block_zero_Vptr: norm.

Definition size_compatible' (n: Z) (p: val) :=
match p with
| Vundef => True
| Vint _ => True
| Vlong _ => True
| Vfloat _ => True
| Vsingle _ => True
| Vptr _ i_ofs => Ptrofs.unsigned i_ofs + n < Ptrofs.modulus
end.

Lemma memory_block_local_facts: forall sh n p, 
  memory_block sh n p |-- !! (isptr p /\ size_compatible' n p).
Proof.
  intros.
   unfold memory_block.
  destruct p; simpl; normalize. apply prop_right;split; auto.
Qed.

Hint Resolve memory_block_local_facts : saturate_local.

Lemma memory_block_offset_zero:
  forall sh n v, memory_block sh n v = memory_block sh n (offset_val 0 v).
Proof.
  intros.
  rewrite <- local_facts_offset_zero.
  reflexivity.
  intro. eapply derives_trans;[ apply memory_block_local_facts | ]. normalize.
Qed.

Lemma memory_block_isptr: forall sh n p, memory_block sh n p = !!(isptr p) && memory_block sh n p.
Proof.
  intros.
  eapply local_facts_isptr.
  + apply memory_block_local_facts.
  + intuition.
Qed.

Lemma memory_block_zero: forall sh p, memory_block sh 0 p = !! isptr p && emp.
Proof.
  intros.
  rewrite memory_block_isptr.
  destruct p;
  try rewrite memory_block_zero_Vptr;
  simpl;
  change (!!False) with FF;
  repeat rewrite FF_andp;
  auto.
Qed.

Lemma access_mode_by_value: forall t, type_is_by_value t = true -> exists ch, access_mode t = By_value ch.
Proof.
  intros.
  assert (forall ch', exists ch, By_value ch' = By_value ch).
    intros. exists ch'. reflexivity.
  destruct t; inversion H; simpl.
  - destruct i, s; apply H0.
  - apply H0.
  - destruct f; apply H0.
  - apply H0.
Qed.

Lemma mapsto_by_value: forall sh t p v, mapsto sh t p v = !! (type_is_by_value t = true) && mapsto sh t p v.
Proof.
  intros.
  apply pred_ext; normalize.
  apply andp_right; [|cancel].
  unfold mapsto.
  destruct t; simpl; normalize; try (apply prop_right; auto).
Qed.

(******************************************

Lemmas from veric

******************************************)

Section COMPSPECS.

Context {cs: compspecs}.

Lemma memory_block_mapsto_:
  forall sh t p,
   type_is_by_value t = true ->
   type_is_volatile t = false ->
   size_compatible t p ->
   align_compatible t p ->
   memory_block sh (sizeof t) p = mapsto_ sh t p.
Proof.
  intros.
  assert (isptr p \/ ~isptr p) by (destruct p; simpl; auto).
  destruct H3. destruct p; try contradiction.
  + simpl in H1, H2.
    destruct (access_mode_by_value _ H) as [ch ?].
    unfold sizeof in *; erewrite size_chunk_sizeof in H1 |- * by eauto.
    rewrite mapsto_memory_block.mapsto__memory_block with (ch := ch); auto.
    eapply align_compatible_rec_by_value_inv in H2; [| eassumption].
    auto.
  + apply pred_ext; saturate_local; try contradiction.
Qed.

Lemma nonreadable_memory_block_mapsto: forall sh p t v,
  ~ readable_share sh ->
  type_is_by_value t = true ->
  type_is_volatile t = false ->
  size_compatible t p ->
  align_compatible t p ->
  tc_val' t v ->
  memory_block sh (sizeof t) p = mapsto sh t p v.
Proof.
  intros.
  apply access_mode_by_value in H0; destruct H0 as [ch ?].
  assert (isptr p \/ ~isptr p) by (destruct p; simpl; auto).
  destruct H5. destruct p; try contradiction.
  + simpl in H2, H3.
    erewrite size_chunk_sizeof in H2 |- * by eauto.
    apply mapsto_memory_block.nonreadable_memory_block_mapsto; auto.
    eapply align_compatible_rec_by_value_inv in H3; [| eassumption].
    auto.
  + apply pred_ext; saturate_local; try contradiction.
Qed.

Lemma memory_block_size_compatible:
  forall sh t p,
  memory_block sh (sizeof t) p = 
  !! (size_compatible t p) && memory_block sh (sizeof t) p.
Proof.
  intros.
  unfold memory_block, size_compatible.
  apply pred_ext; destruct p; normalize.
Qed.

Global Opaque memory_block.

End COMPSPECS.

(******************************************

Lemmas about specific types

******************************************)

(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto _ _ _ _) =>
   (simple apply mapsto_mapsto_int32; apply Coq.Init.Logic.I)  : cancel.

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto_ _ _ _) =>
   (simple apply mapsto_mapsto__int32; apply Coq.Init.Logic.I)  : cancel.

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto_ _ _ _) =>
    (apply mapsto_mapsto_) : cancel.

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto_ _ _ _) =>
   (apply mapsto_mapsto__int32)  : cancel.

Hint Extern 1 (mapsto _ _ _ _ |-- mapsto _ _ _ _) =>
   (apply mapsto_mapsto_int32)  : cancel.

Hint Extern 0 (legal_alignas_type _ = true) => reflexivity : cancel.

Lemma mapsto_force_ptr: forall sh t v v',
  mapsto sh t (force_ptr v) v' = mapsto sh t v v'.
Proof.
intros.
destruct v; simpl; auto.
Qed.

Hint Rewrite mapsto_force_ptr: norm.

(******************************************

Definition of at_offset.

at_offset is the elementary definition. All useful lemmas about at_offset will be proved here.

******************************************)

Definition at_offset (P: val -> mpred) (z: Z): val -> mpred :=
 fun v => P (offset_val z v).

Arguments at_offset P z v : simpl never.

Lemma at_offset_eq: forall P z v,
  at_offset P z v = P (offset_val z v).
Proof.
intros; auto.
Qed.

Lemma lifted_at_offset_eq: forall (P: val -> mpred) z v,
  `(at_offset P z) v = `P (`(offset_val z) v).
Proof.
  intros.
  unfold liftx, lift in *. simpl in *.
  extensionality p.
  apply at_offset_eq.
Qed.

Lemma at_offset_eq2: forall pos pos' P,
  forall p, at_offset P (pos + pos') p = at_offset P pos' (offset_val pos p).
Proof.
  intros.
  rewrite at_offset_eq.
  rewrite at_offset_eq.
  unfold offset_val.
  destruct p; auto.
  rewrite ptrofs_add_assoc1.
  reflexivity.
Qed.

Lemma at_offset_eq3: forall P z b ofs,
  at_offset P z (Vptr b (Ptrofs.repr ofs)) = P (Vptr b (Ptrofs.repr (ofs + z))).
Proof.
  intros.
  rewrite at_offset_eq.
  unfold offset_val.
  solve_mod_modulus.
  reflexivity.
Qed.

Lemma at_offset_derives: forall P Q p , (forall p, P p |-- Q p) -> forall pos, at_offset P pos p |-- at_offset Q pos p.
Proof.
  intros.
  rewrite !at_offset_eq.
  apply H.
Qed.

(******************************************

Definitions of spacer and withspacer

Comment: spacer only has offset_zero property but does not have local_facts
and isptr property.

******************************************)

Definition spacer (sh: share) (be: Z) (ed: Z) : val -> mpred :=
  if Z.eq_dec (ed - be) 0
  then fun _ => emp
  else
    at_offset (memory_block sh (ed - be)) be.
(* Arguments spacer sh be ed / _ . *)

Definition withspacer sh (be: Z) (ed: Z) P (p: val): mpred :=
   if Z.eq_dec (ed - be) 0
   then P p
   else P p * spacer sh be ed p.

Lemma withspacer_spacer: forall sh be ed P p,
   withspacer sh be ed P p = spacer sh be ed p * P p.
Proof.
  intros.
  unfold withspacer, spacer.
  if_tac.
  + normalize.
  + simpl; apply sepcon_comm.
Qed.

Lemma withspacer_ramif_Q: forall sh be ed P p,
  withspacer sh be ed P p |-- P p *
    allp ((fun Q => Q p) -* (fun Q => withspacer sh be ed Q p)).
Proof.
  intros.
  apply RAMIF_Q.solve with (spacer sh be ed p).
  + rewrite withspacer_spacer.
    cancel.
  + intros.
    rewrite withspacer_spacer.
    cancel.
Qed.

Lemma spacer_offset_zero:
  forall sh be ed v, spacer sh be ed v = spacer sh be ed (offset_val 0 v).
Proof.
  intros;
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);  auto.
  repeat rewrite at_offset_eq;
  try rewrite offset_offset_val; try  rewrite Int.add_zero_l; auto.
Qed.

Lemma withspacer_add:
  forall sh pos be ed P p,
  withspacer sh (pos + be) (pos + ed) (fun p0 => P (offset_val pos p)) p =
  withspacer sh be ed P (offset_val pos p).
Proof.
  intros.
  rewrite !withspacer_spacer.
  unfold spacer.
  simpl.
  replace (pos + ed - (pos + be)) with (ed - be) by omega.
  if_tac; [reflexivity|].
  rewrite !at_offset_eq.
  replace (offset_val (pos + be) p) with
          (offset_val be (offset_val pos p)).
  reflexivity.
  destruct p; simpl; try reflexivity.
  rewrite ptrofs_add_assoc1.
  reflexivity.
Qed.

Lemma offset_val_preserve_isptr: forall p pos, !! (isptr (offset_val pos p)) |-- !! (isptr p).
Proof.
  intros.
  destruct p; simpl; apply derives_refl.
Qed.

Lemma at_offset_preserve_local_facts: forall P pos, (forall p, P p |-- !!(isptr p)) -> (forall p, at_offset P pos p |-- !!(isptr p)).
Proof.
  intros.
  rewrite at_offset_eq.
  specialize (H (offset_val pos p)).
  eapply derives_trans; [exact H |].
  apply offset_val_preserve_isptr.
Qed.

Lemma withspacer_preserve_local_facts: forall sh be ed P, (forall p, P p |-- !! (isptr p)) -> (forall p, withspacer sh be ed P p |-- !! (isptr p)).
Proof.
  intros.
  rewrite withspacer_spacer.
  simpl; rewrite sepcon_comm.
  apply (derives_left_sepcon_right_corable (!!isptr p) (P p) _); [apply corable_prop|].
  apply H.
Qed.

Transparent memory_block.

Lemma spacer_memory_block:
  forall sh be ed v, isptr v ->
 spacer sh be ed v = memory_block sh (ed - be) (offset_val be v).
Proof.
  intros.
  destruct v; inv H.
  unfold spacer.
  destruct (Z.eq_dec (ed - be) 0);
  try solve [rewrite e; simpl offset_val; rewrite memory_block_zero_Vptr; auto].
  rewrite at_offset_eq.
  destruct be; auto.
Qed.

Lemma spacer_sepcon_memory_block: forall sh ofs lo hi b i,
  0 <= lo ->
  0 <= ofs ->
  lo <= hi < Ptrofs.modulus ->
  Ptrofs.unsigned i + ofs + hi < Ptrofs.modulus ->
  spacer sh (ofs + lo) (ofs + hi) (Vptr b i) * memory_block sh lo (offset_val ofs (Vptr b i)) = memory_block sh hi (offset_val ofs (Vptr b i)).
Proof.
  intros.
  rewrite spacer_memory_block by (simpl; auto).
  simpl offset_val.
  inv_int i.
  rewrite !ptrofs_add_repr.
  rewrite sepcon_comm, Z.add_assoc, <- memory_block_split by omega.
  f_equal.
  omega.
Qed.

Hint Rewrite at_offset_eq3 : at_offset_db.
Hint Rewrite withspacer_spacer : at_offset_db.
Hint Rewrite spacer_memory_block using (simpl; auto): at_offset_db.

Opaque memory_block.

