Require Import floyd.proofauto.
Require Import progs.bst.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.

Section TREES.
Variable V : Type.
Variable default: V.

Definition key := Z.

Inductive tree : Type :=
 | E : tree
 | T: tree -> key -> V -> tree -> tree.

Definition empty_tree : tree := E.

Fixpoint lookup (x: key) (t : tree) : V :=
  match t with
  | E => default
  | T tl k v tr => if x <? k then lookup x tl 
                         else if k <? x then lookup x tr
                         else v
  end.

Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with 
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v b
 end.

End TREES.
Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments lookup {V} default x t.

Fixpoint tree_rep (t: tree val) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) && 
    EX pa:val, EX pb:val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
    tree_rep a pa * tree_rep b pb
 end.

Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree) p b * tree_rep t p.

Definition mallocN_spec :=
 DECLARE _mallocN
  WITH n: Z
  PRE [ 1%positive OF tint]
     PROP (4 <= n <= Int.max_unsigned) 
     LOCAL (temp 1%positive (Vint (Int.repr n)))
     SEP ()
  POST [ tptr tvoid ] 
     EX v: val,
     PROP (malloc_compatible n v) 
     LOCAL (temp ret_temp v) 
     SEP (memory_block Tsh n v).

Definition freeN_spec :=
 DECLARE _freeN
  WITH p : val , n : Z
  PRE [ 1%positive OF tptr tvoid , 2%positive OF tint]  
     (* we should also require natural_align_compatible (eval_id 1) *)
      PROP() LOCAL (temp 1%positive p; temp 2%positive (Vint (Int.repr n)))
      SEP (memory_block Tsh n p)
  POST [ tvoid ]  
    PROP () LOCAL () SEP ().

Definition treebox_new_spec :=
 DECLARE _treebox_new
  WITH u : unit
  PRE  [  ]
       PROP() LOCAL() SEP ()
  POST [ (tptr t_struct_tree) ] 
    EX v:val,
    PROP()
    LOCAL(temp ret_temp v)
    SEP (data_at Tsh (tptr t_struct_tree) nullval v).

Definition insert_spec :=
 DECLARE _insert
  WITH b: val, x: Z, v: val, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint,
        _value OF (tptr Tvoid)   ]
    PROP( Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)); temp _value v)
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
   EX p':val,
    PROP()
    LOCAL()
    SEP (treebox_rep (insert x v t) b).

Definition lookup_spec :=
 DECLARE _lookup
  WITH b: val, x: Z, v: val, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint  ]
    PROP( Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (treebox_rep t b)
  POST [ tptr Tvoid ] 
    PROP()
    LOCAL(temp ret_temp (lookup nullval x t))
    SEP (treebox_rep t b).

Definition tree_free_spec :=
 DECLARE _tree_free
  WITH t: tree val, p: val
  PRE  [ _p OF (tptr t_struct_tree) ]
       PROP() LOCAL(temp _p p) SEP (tree_rep t p)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (emp).

Definition treebox_free_spec :=
 DECLARE _treebox_free
  WITH t: tree val, b: val
  PRE  [ _b OF (tptr (tptr t_struct_tree)) ]
       PROP() LOCAL(temp _b b) SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (emp).

Definition Gprog : funspecs := 
    ltac:(with_library prog [
    mallocN_spec; freeN_spec; treebox_new_spec; 
    tree_free_spec; treebox_free_spec;
    insert_spec; lookup_spec
  ]).

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

Definition insert_inv (b0: val) (t0: tree val) (x: Z) (v: val): environ -> mpred :=
  EX b: val, EX t: tree val, 
  PROP() 
  LOCAL(temp _t b; temp _x (Vint (Int.repr x));   temp _value v)
  SEP(treebox_rep t b;  (treebox_rep (insert x v t) b -* treebox_rep (insert x v t0) b0)).

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
 eapply semax_pre; [ 
    | apply (semax_loop _ (insert_inv b t x v) (insert_inv b t x v) )].
 unfold insert_inv.
*
 Exists b t. entailer.
 rewrite <- sepcon_emp at 1.
 apply sepcon_derives; auto. 
 apply wand_sepcon_adjoint. 
 entailer!.
*
 forward. (* Sskip *)
 unfold insert_inv.
 Intros b1 t1.
 unfold treebox_rep at 1. Intros p1.
 forward. (* p = *t; *)
 forward_if.
 + (* then clause *)
 subst p1.
 forward_call (sizeof t_struct_tree). simpl; repable_signed.
 Intros p'.
 rewrite memory_block_data_at_ by auto.
 forward. (* p->key=x; *)
 simpl.
 forward. (* p->value=value; *)
 forward. (*p->left=NULL; *)
 forward. (*p->right=NULL; *)
 assert_PROP (t1= (@E _)). {
   destruct t1. entailer!. simpl tree_rep.
  Intros pa pb. entailer!.
  destruct H8; contradiction.
 }
 subst t1. simpl tree_rep. rewrite !prop_true_andp by auto.
 replace  (force_val (sem_cast_neutral v)) with v 
   by (clear - H0; destruct v; try contradiction; reflexivity).
 forward. (* *t = p; *)
 forward. (* return; *)
 match goal with |- _ * ?B * ?C |-- _ => 
 apply derives_trans with 
    (treebox_rep (T E x v E) b1 * C)
 end.
 cancel.
 unfold treebox_rep, tree_rep. Exists p' nullval nullval. entailer!.
 rewrite sepcon_comm.
 apply wand_sepcon_adjoint. auto.
 + (* else clause *)
 destruct t1.
 simpl tree_rep. normalize. contradiction H1; auto.
 simpl tree_rep.
 Intros pa pb. clear H1.
 forward.
 forward_if; [ | forward_if ].
  - (* Inner if, then clause: x<k *)
    forward.
    unfold insert_inv.
    Exists (offset_val 8 p1) t1_1.
    entailer!.
    replace (x<?k) with true by (symmetry; apply Z.ltb_lt; omega).
   replace (offset_val 8 p1) with (field_address t_struct_tree [StructField _left] p1)
     by (unfold field_address; simpl; rewrite if_true by auto with field_compatible; auto).
  apply RAMIF_PLAIN.trans'.
  unfold_data_at 2%nat.
  rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
   match goal with |- ?A * (?Bk * (?Bv * (?Ba * ?Bb))) * ?Ta * ?Tb |-- _ =>
      apply derives_trans 
      with (treebox_rep t1_1 (field_address t_struct_tree [StructField _left] p1) *
               A * Bk * Bv * Bb * Tb)
   end.
   unfold treebox_rep at 1. Exists pa. cancel.
   cancel.
   rewrite <- wand_sepcon_adjoint.
   unfold treebox_rep. Intros pa'. Exists p1. simpl tree_rep. Exists pa' pb.
   entailer!. unfold_data_at 2%nat.
   rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
   cancel.
 - (* Inner if, second branch:  k<x *)
  forward.
  unfold insert_inv.
  Exists (offset_val 12 p1) t1_2.
  entailer!.
  replace (x<?k) with false by (symmetry; apply Z.ltb_ge; omega).
  replace (k<?x) with true by (symmetry; apply Z.ltb_lt; omega).
  replace (offset_val 12 p1) with (field_address t_struct_tree [StructField _right] p1)
     by (unfold field_address; simpl; rewrite if_true by auto with field_compatible; auto).
  apply RAMIF_PLAIN.trans'.
  unfold_data_at 2%nat.
   rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
   match goal with |- ?A * (?Bk * (?Bv * (?Ba * ?Bb))) * ?Ta * ?Tb |-- _ =>
      apply derives_trans 
      with (treebox_rep t1_2 (field_address t_struct_tree [StructField _right] p1) *
               A * Bk * Bv * Ba * Ta)
   end.
   unfold treebox_rep at 1. Exists pb. cancel.
   cancel.
   rewrite <- wand_sepcon_adjoint.
   unfold treebox_rep. Intros pb'. Exists p1. simpl tree_rep. Exists pa pb'.
   entailer!. unfold_data_at 2%nat.
   rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
   cancel.
 - (* Inner if, third branch: x=k *)
   assert (x=k) by omega.
   subst x. clear H H1 H4.
   forward.
   forward.
   replace (k <? k) with false by (symmetry; apply Z.ltb_ge; omega).
   apply modus_ponens_wand'.
   unfold treebox_rep. Exists p1. simpl tree_rep. Exists pa pb. entailer!.
* (* After the loop *)
  forward.
  simpl loop2_ret_assert. apply andp_left2. auto.
Qed.

Definition lookup_inv (b0 p0: val) (t0: tree val) (x: Z): environ -> mpred :=
  EX p: val, EX t: tree val, 
  PROP(lookup nullval x t = lookup nullval x t0) 
  LOCAL(temp _p p; temp _t b0; temp _x (Vint (Int.repr x)))
  SEP(data_at Tsh (tptr t_struct_tree) p0 b0; tree_rep t p;  (tree_rep t p -* tree_rep t0 p0)).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold treebox_rep. Intros p.
  forward.
  forward_while (lookup_inv b p t x).
* (* precondition implies loop invariant *)
  Exists p t. entailer!.
  apply -> wand_sepcon_adjoint. cancel.
* (* type-check loop condition *)
  entailer!.
* (* loop body preserves invariant *)
  destruct t0; unfold tree_rep at 1; fold tree_rep. normalize. contradiction HRE; auto.
  Intros pa pb.
  forward.
  forward_if; [ | forward_if ].
 + (* then clause: x<y *)
   forward.
  Exists (pa,t0_1). unfold fst,snd.
  set (tr := tree_rep (T t0_1 k v0 t0_2) p0).
  entailer!.
  rewrite <- H0; simpl.
  replace (x<?k) with true by (symmetry; apply Z.ltb_lt; omega). auto.
  apply -> wand_sepcon_adjoint.
  pull_right (tr -* tree_rep t p).
  apply modus_ponens_wand'.
  subst tr. simpl. Exists pa pb. entailer!.
 + (* else-then clause: y<x *)
   forward.
   Exists (pb,t0_2). unfold fst,snd.
  set (tr := tree_rep (T t0_1 k v0 t0_2) p0).
  entailer!.
  rewrite <- H0; simpl.
  replace (x<?k) with false by (symmetry; apply Z.ltb_ge; omega).
  replace (k<?x) with true by (symmetry; apply Z.ltb_lt; omega). auto.
  apply -> wand_sepcon_adjoint.
  pull_right (tr -* tree_rep t p).
  apply modus_ponens_wand'.
  subst tr. simpl. Exists pa pb. entailer!.
 + (* else-else clause: x=y *)
  assert (x=k) by omega. subst x. clear H H4 H5.
  forward.
  set (tr := tree_rep (T t0_1 k v0 t0_2) p0).
  forward.
  unfold treebox_rep. Exists p.
  entailer!. rewrite <- H0. simpl.
  replace (k <? k) with false by (symmetry; apply Z.ltb_ge; omega). auto.
  apply modus_ponens_wand'.
  subst tr. simpl. Exists pa pb. entailer!.
* (* after the loop *)
  forward.
  unfold treebox_rep. Exists p.
  destruct t0; simpl tree_rep.
  entailer!.
  rewrite <- (emp_sepcon (_ -* _)). apply modus_ponens_wand.
  Intros pa pb.  entailer. destruct H5; contradiction.
Qed.

Lemma body_treebox_new: semax_body Vprog Gprog f_treebox_new treebox_new_spec.
Proof.
  start_function.
  forward_call (sizeof (tptr t_struct_tree)).
  simpl sizeof; computable.
  Intros p.
  rewrite memory_block_data_at_ by auto.
  forward.
  forward.
  Exists p. entailer!.
Qed.


Lemma body_tree_free: semax_body Vprog Gprog f_tree_free tree_free_spec.
Proof.
  start_function.
  forward_if (PROP()LOCAL()SEP()).
  destruct t; simpl tree_rep. Intros. contradiction.
  Intros pa pb.
  forward.
  forward.
  forward_call (p, sizeof t_struct_tree).
  entailer!.
  rewrite memory_block_data_at_ by auto.
  cancel.
  forward_call (t1,pa).
  forward_call (t2,pb).
  entailer!.
  forward.
  subst.
  entailer!.
  destruct t; simpl; normalize.
  entailer!.
  destruct H1; contradiction.
  forward.
Qed.

Lemma body_treebox_free: semax_body Vprog Gprog f_treebox_free treebox_free_spec.
Proof.
  start_function.
  unfold treebox_rep.
  Intros p.
  forward.
  forward_call (t,p).
  forward_call (b, sizeof (tptr t_struct_tree)).
  entailer!.
  rewrite memory_block_data_at_ by auto.
  cancel.
  forward.
Qed.















