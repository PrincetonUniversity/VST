Require Import VST.floyd.proofauto.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
Require Import WandDemo.wand_frame.
Require Import WandDemo.wandQ_frame.
Require Import WandDemo.bst.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
Definition t_struct_tree := Tstruct _tree noattr.

Fixpoint tree_rep (t: tree val) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= Z.of_nat x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat x)),(v,(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.

Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.

(*
(* TODO: seems not useful *)
Lemma treebox_rep_spec: forall (t: tree val) (b: val),
  treebox_rep t b =
  EX p: val, 
  match t with
  | E => !!(p=nullval) && data_at Tsh (tptr t_struct_tree) p b
  | T l x v r => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
      data_at Tsh (tptr t_struct_tree) p b *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
      field_at Tsh t_struct_tree [StructField _value] v p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.
Proof.
  intros.
  unfold treebox_rep at 1.
  f_equal.
  extensionality p.
  destruct t; simpl.
  + apply pred_ext; entailer!.
  + unfold treebox_rep.
    apply pred_ext; entailer!.
    - Intros pa pb.
      Exists pb pa.
      unfold_data_at 1%nat.
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
    - Intros pa pb.
      Exists pb pa.
      unfold_data_at 3%nat.
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      cancel.
Qed.


*)


Lemma tree_rep_saturate_local:
   forall t p, tree_rep t p |-- !! is_pointer_or_null p.
Proof.
destruct t; simpl; intros.
entailer!.
Intros pa pb. entailer!.
Qed.

Hint Resolve tree_rep_saturate_local: saturate_local.

Lemma tree_rep_valid_pointer:
  forall t p, tree_rep t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve tree_rep_valid_pointer: valid_pointer.

Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree) [] b.
Proof.
intros.
unfold treebox_rep.
Intros p.
entailer!.
Qed.

Hint Resolve treebox_rep_saturate_local: saturate_local.

Lemma tree_rep_nullval: forall t,
  tree_rep t nullval |-- !! (t = E).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl tree_rep.
  Intros pa pb. entailer!.
Qed.

Hint Resolve tree_rep_nullval: saturate_local.

Lemma treebox_rep_leaf: forall x p b (v: val),
  is_pointer_or_null v ->
  Int.min_signed <= Z.of_nat x <= Int.max_signed ->
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat x)), (v, (nullval, nullval))) p * data_at Tsh (tptr t_struct_tree) p b |-- treebox_rep (T E x v E) b.
Proof.
  intros.
  unfold treebox_rep, tree_rep. Exists p nullval nullval. entailer!.
Qed.

Module PartialTreeboxRep_WandFrame.

Lemma partial_treebox_rep_singleton_left: forall (t1 t1' t2: tree val) k (v p1 p2 p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat k)), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t1 (field_address t_struct_tree [StructField _left] p) *
       (treebox_rep t1'
         (field_address t_struct_tree [StructField _left] p) -*
        treebox_rep (T t1' k v t2) b).
Proof.
  intros.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  cancel.
Qed.

Lemma partial_treebox_rep_singleton_right: forall (t1 t2 t2': tree val) k (v p1 p2 p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat k)), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t2 (field_address t_struct_tree [StructField _right] p) *
       (treebox_rep t2'
         (field_address t_struct_tree [StructField _right] p) -*
        treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  cancel.
Qed.

Lemma partial_treebox_rep_partial_tree_rep: forall t1 t2 t3 p1 p2 p3,
  (treebox_rep t1 p1 -* treebox_rep t2 p2) * (treebox_rep t2 p2 -* treebox_rep t3 p3) |-- treebox_rep t1 p1 -* treebox_rep t3 p3.
Proof.
  intros.
  apply wand_frame_ver.
Qed.

End PartialTreeboxRep_WandFrame.

Module PartialTreeboxRep_WandQFrame.

Definition partial_treebox_rep (pt: partial_tree val) (p_root p_in: val): mpred :=
  ALL t: tree val, treebox_rep t p_in -* treebox_rep (partial_tree_tree pt t) p_root.

Lemma partial_treebox_rep_singleton_left: forall (t1 t1' t2: tree val) k (v p1 p2 p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat k)), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t1 (field_address t_struct_tree [StructField _left] p) *
       (treebox_rep t1'
         (field_address t_struct_tree [StructField _left] p) -*
        treebox_rep (T t1' k v t2) b).
Proof.
  intros.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  unfold treebox_rep at 1. Exists p1. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p1.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p1.
  Exists p1 p2.
  entailer!.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
  cancel.
Qed.

Lemma partial_treebox_rep_singleton_right: forall (t1 t2 t2': tree val) k (v p1 p2 p b: val),
  Int.min_signed <= Z.of_nat k <= Int.max_signed ->
  is_pointer_or_null v ->
  data_at Tsh (tptr t_struct_tree) p b *
  data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat k)), (v, (p1, p2))) p *
  tree_rep t1 p1 * tree_rep t2 p2
  |-- treebox_rep t2 (field_address t_struct_tree [StructField _right] p) *
       (treebox_rep t2'
         (field_address t_struct_tree [StructField _right] p) -*
        treebox_rep (T t1 k v t2') b).
Proof.
  intros.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  unfold treebox_rep at 1. Exists p2. cancel.

  rewrite <- wand_sepcon_adjoint.
  clear p2.
  unfold treebox_rep.
  Exists p.
  simpl.
  Intros p2.
  Exists p1 p2.
  entailer!.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
  cancel.
Qed.

Lemma partial_treebox_rep_partial_tree_rep: forall t1 t2 t3 p1 p2 p3,
  (treebox_rep t1 p1 -* treebox_rep t2 p2) * (treebox_rep t2 p2 -* treebox_rep t3 p3) |-- treebox_rep t1 p1 -* treebox_rep t3 p3.