Require Import VST.floyd.proofauto.
Require Import VFA.Maps.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
Require Import WandDemo.bst.
Require Import WandDemo.bst_lemmas.
Require Import WandDemo.VST_lemmas.

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

Definition insert_spec :=
 DECLARE _insert
  WITH p0: val, x: nat, v: val, m0: total_map val
  PRE  [ _p OF (tptr (tptr t_struct_tree)), _x OF tint,
        _value OF (tptr Tvoid)   ]
    PROP( Int.min_signed <= Z.of_nat x <= Int.max_signed; is_pointer_or_null v)
    LOCAL(temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)
    SEP (Mapbox_rep m0 p0)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (Mapbox_rep (t_update m0 x v) p0).

Definition lookup_spec :=
 DECLARE _lookup
  WITH p0: val, x: nat, v: val, t0: tree val
  PRE  [ _p OF (tptr (tptr t_struct_tree)), _x OF tint  ]
    PROP( Int.min_signed <= Z.of_nat x <= Int.max_signed)
    LOCAL(temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))))
    SEP (treebox_rep t0 p0)
  POST [ tptr Tvoid ]
    PROP()
    LOCAL(temp ret_temp (lookup nullval x t0))
    SEP (treebox_rep t0 p0).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH ta: tree val, x: nat, vx: val, tb: tree val, y: nat, vy: val, tc: tree val, b: val, l: val, pa: val, r: val
  PRE  [ __l OF (tptr (tptr (Tstruct _tree noattr))),
        _l OF (tptr (Tstruct _tree noattr)),
        _r OF (tptr (Tstruct _tree noattr))]
    PROP(Int.min_signed <= Z.of_nat x <= Int.max_signed; is_pointer_or_null vx)
    LOCAL(temp __l b; temp _l l; temp _r r)
    SEP (data_at Tsh (tptr t_struct_tree) l b;
         data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat x)), (vx, (pa, r))) l;
         tree_rep ta pa;
         tree_rep (T tb y vy tc) r)
  POST [ Tvoid ] 
    EX pc: val,
    PROP(Int.min_signed <= Z.of_nat y <= Int.max_signed; is_pointer_or_null vy)
    LOCAL()
    SEP (data_at Tsh (tptr t_struct_tree) r b;
         data_at Tsh t_struct_tree (Vint (Int.repr (Z.of_nat y)), (vy, (l, pc))) r;
         tree_rep (T ta x vx tb) l;
         tree_rep tc pc).

Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH ta: tree val, x: nat, v: val, tb: tree val, b: val, p: val
  PRE  [ _t OF (tptr (tptr (Tstruct _tree noattr)))]
    PROP(Int.min_signed <= Z.of_nat x <= Int.max_signed; tc_val (tptr Tvoid) v)
    LOCAL(temp _t b)
    SEP (data_at Tsh (tptr t_struct_tree) p b;
         field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr (Z.of_nat x))) p;
         field_at Tsh t_struct_tree [StructField _value] v p;
         treebox_rep ta (field_address t_struct_tree [StructField _left] p);
         treebox_rep tb (field_address t_struct_tree [StructField _right] p))
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (pushdown_left ta tb) b).

Definition delete_spec :=
 DECLARE _delete
  WITH b: val, x: nat, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP( Int.min_signed <= Z.of_nat x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr (Z.of_nat x))))
    SEP (treebox_rep t b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (delete x t) b).

Definition Gprog : funspecs :=
    ltac:(with_library prog [
    mallocN_spec; freeN_spec;
    insert_spec; lookup_spec;
    turn_left_spec; pushdown_left_spec; delete_spec
  ]).

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply NPeano.Nat.ltb_lt; rewrite Nat2Z.inj_lt; omega)
                          | rewrite if_falseb by (apply NPeano.Nat.ltb_nlt; rewrite Nat2Z.inj_lt; omega)].

Module insert_by_WandQFrame_Func_Hole.

Import PartialTreeboxRep_WandQFrame_Func_Hole.

Definition insert_inv (p0: val) (t0: tree val) (x: nat) (v: val): environ -> mpred :=
  EX p: val, EX t: tree val, EX P: tree val -> tree val,
  PROP(P (insert x v t) = (insert x v t0))
  LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
  SEP(treebox_rep t p;  partial_treebox_rep P p0 p).

Ltac forward_loop Inv :=
 eapply semax_pre; [ | apply (semax_loop _ Inv Inv); [ |  apply sequential; apply semax_skip]] .

Lemma insert_concrete_to_abstract:
 forall {Espec: OracleKind} CMD p0 x v m0,
 (forall t0, 
   semax (func_tycontext f_insert Vprog Gprog [])
    (PROP ( )
     LOCAL (temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)  
     SEP (treebox_rep t0 p0)) CMD
   (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP ( )  LOCAL ()  SEP (treebox_rep (insert x v t0) p0))) emp))  ->
 semax (func_tycontext f_insert Vprog Gprog [])
   (PROP ( )
    LOCAL (temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))); temp _value v)
    SEP (Mapbox_rep m0 p0)) CMD
  (frame_ret_assert
    (function_body_ret_assert tvoid
     (PROP ( )  LOCAL ()  SEP (Mapbox_rep (t_update m0 x v) p0))) emp).
Proof.
  intros.
  rewrite !Mapbox_rep_unfold.
  Intros t0.
  apply (semax_post'' (PROP () LOCAL () SEP (treebox_rep (insert x v t0) p0))); auto.
  Exists (insert x v t0).
  entailer!.
  split; [apply insert_relate | apply insert_SearchTree]; auto.
Qed.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  apply insert_concrete_to_abstract; intros.
  forward_loop (EX p: val, EX t: tree val, EX P: tree val -> tree val,
       PROP(P (insert x v t) = (insert x v t0))
       LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
       SEP(treebox_rep t p;  partial_treebox_rep P p0 p)).
  * (* Precondition *)
    Exists p0 t0 (fun t: tree val => t). entailer!.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    Intros p t P.
    forward. (* Sskip *)
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)) by entailer!.
      subst t. rewrite tree_rep_treebox_rep. normalize.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.  clear - H1 H0 H.
      sep_apply (treebox_rep_leaf x q p v); auto.
      rewrite <- H1. apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H2.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        Exists (field_address t_struct_tree [StructField _left] q) t1 (fun t1 => P (T t1 k v0 t2)).
        entailer!.
       ** rewrite <- H1.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        Exists (field_address t_struct_tree [StructField _right] q) t2 (fun t2 => P (T t1 k v0 t2)).
        entailer!.
       ** rewrite <- H1.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
          cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H2 H5.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        rewrite <- H1.
        simpl insert. simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
Qed.

End insert_by_WandQFrame_Func_Hole.

Module insert_by_WandFrame.

Import PartialTreeboxRep_WandFrame.

Definition insert_inv (p0: val) (t0: tree val) (x: nat) (v: val): environ -> mpred :=
  EX p: val, EX t: tree val,
  PROP()
  LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
  SEP(treebox_rep t p;  (treebox_rep (insert x v t) p -* treebox_rep (insert x v t0) p0)).

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  rewrite Mapbox_rep_unfold.
  Intros t0.
  apply (semax_post'' (PROP () LOCAL () SEP (treebox_rep (insert x v t0) p0))); auto.
  { rewrite Mapbox_rep_unfold; Exists (insert x v t0).
    entailer!.
    split; [apply insert_relate | apply insert_SearchTree]; auto. }
  clear H1 H2.
  eapply semax_pre; [
    | apply (semax_loop _ (insert_inv p0 t0 x v) (insert_inv p0 t0 x v) )].
  * (* Precondition *)
    unfold insert_inv.
    Exists p0 t0. entailer.
    apply ramify_PPQQ.
  * (* Loop body *)
    unfold insert_inv.
    Intros p t.
    forward. (* Sskip *)
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      simpl.
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)).
        1: entailer!.
      subst t. rewrite tree_rep_treebox_rep. rewrite !prop_true_andp by auto.
      rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.
      sep_apply (treebox_rep_leaf x q p v); auto.
      apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H1.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _left] q) t1.
        entailer!.
        simpl_compb.
        sep_apply (partial_treebox_rep_singleton_left (insert x v t1) t2 k v0 q p); auto.
        cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _right] q) t2.
        entailer!.
        simpl_compb; simpl_compb.
        sep_apply (partial_treebox_rep_singleton_right t1 (insert x v t2) k v0 q p); auto.
        cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H1 H4.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize. 
Qed.

End insert_by_WandFrame.

Module insert_by_WandQFrame_Ind_Hole.

Import PartialTreeboxRep_WandQFrame_Ind_Hole.

Definition insert_inv (p0: val) (t0: tree val) (x: nat) (v: val): environ -> mpred :=
  EX p: val, EX t: tree val, EX pt: partial_tree val,
  PROP(partial_tree_tree pt (insert x v t) = (insert x v t0))
  LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
  SEP(treebox_rep t p;  partial_treebox_rep pt p0 p).

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  rewrite Mapbox_rep_unfold.
  Intros t0.
  apply (semax_post'' (PROP () LOCAL () SEP (treebox_rep (insert x v t0) p0))); auto.
  { rewrite Mapbox_rep_unfold; Exists (insert x v t0).
    entailer!.
    split; [apply insert_relate | apply insert_SearchTree]; auto. }
  clear H1 H2.
  eapply semax_pre; [
    | apply (semax_loop _ (insert_inv p0 t0 x v) (insert_inv p0 t0 x v) )].
  * (* Precondition *)
    unfold insert_inv.
    Exists p0 t0 (@SearchTree_ext.H val). entailer.
    cancel.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    unfold insert_inv.
    Intros p t pt.
    forward. (* Sskip *)
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      simpl.
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)).
        1: entailer!.
      subst t. rewrite tree_rep_treebox_rep. rewrite !prop_true_andp by auto.
      rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.
      sep_apply (treebox_rep_leaf x q p v); auto.
      rewrite <- H1. apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H2.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _left] q) t1 (partial_tree_partial_tree pt (SearchTree_ext.L SearchTree_ext.H k v0 t2)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _right] q) t2 (partial_tree_partial_tree pt (SearchTree_ext.R t1 k v0 SearchTree_ext.H)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
          cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H2 H5.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        rewrite <- H1.
        simpl insert.
        simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize. 
Qed.

End insert_by_WandQFrame_Ind_Hole.

Module insert_by_Ind_Pred_Ind_Hole.

Import PartialTreeboxRep_Ind_Pred_Ind_Hole.

Definition insert_inv (p0: val) (t0: tree val) (x: nat) (v: val): environ -> mpred :=
  EX p: val, EX t: tree val, EX pt: partial_tree val,
  PROP(partial_tree_tree pt (insert x v t) = (insert x v t0))
  LOCAL(temp _p p; temp _x (Vint (Int.repr (Z.of_nat x)));   temp _value v)
  SEP(treebox_rep t p; partial_treebox_rep pt p0 p).

Opaque partial_treebox_rep.
Arguments partial_treebox_rep: simpl never.

Lemma body_insert: semax_body Vprog Gprog f_insert insert_spec.
Proof.
  start_function.
  rewrite Mapbox_rep_unfold.
  Intros t0.
  apply (semax_post'' (PROP () LOCAL () SEP (treebox_rep (insert x v t0) p0))); auto.
  { rewrite Mapbox_rep_unfold; Exists (insert x v t0).
    entailer!.
    split; [apply insert_relate | apply insert_SearchTree]; auto. }
  clear H1 H2.
  eapply semax_pre; [
    | apply (semax_loop _ (insert_inv p0 t0 x v) (insert_inv p0 t0 x v) )].
  * (* Precondition *)
    unfold insert_inv.
    Exists p0 t0 (@SearchTree_ext.H val). entailer.
    cancel.
    apply emp_partial_treebox_rep_H.
  * (* Loop body *)
    unfold insert_inv.
    Intros p t pt.
    forward. (* Sskip *)
    rewrite treebox_rep_tree_rep at 1. Intros q.
    forward. (* q = * p; *)
    forward_if.
    + (* then clause *)
      subst q.
      forward_call (sizeof t_struct_tree).
        1: simpl; rep_omega.
      Intros q.
      rewrite memory_block_data_at_ by auto.
      forward. (* q->key=x; *)
      simpl.
      forward. (* q->value=value; *)
      forward. (* q->left=NULL; *)
      forward. (* q->right=NULL; *)
      assert_PROP (t = (@E _)).
        1: entailer!.
      subst t. rewrite tree_rep_treebox_rep. rewrite !prop_true_andp by auto.
      rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
      forward. (* * p = q; *)
      forward. (* return; *)
      entailer!.
      sep_apply (treebox_rep_leaf x q p v); auto.
      rewrite <- H1. apply treebox_rep_partial_treebox_rep.
    + (* else clause *)
      destruct t; rewrite tree_rep_treebox_rep.
      { normalize. }
      Intros. clear H2.
      forward. (* y=q->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* p=&q->left *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _left] q) t1 (partial_tree_partial_tree pt (SearchTree_ext.L SearchTree_ext.H k v0 t2)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_left t2 k v0 q p); auto.
          apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, second branch:  k<x *)
        forward. (* p=&q->right *)
        unfold insert_inv.
        Exists (field_address t_struct_tree [StructField _right] q) t2 (partial_tree_partial_tree pt (SearchTree_ext.R t1 k v0 SearchTree_ext.H)).
        entailer!.
       ** rewrite partial_tree_partial_tree_tree.
          rewrite <- H1.
          simpl; simpl_compb; simpl_compb; auto.
       ** sep_apply (partial_treebox_rep_singleton_right t1 k v0 q p); auto.
          cancel; apply partial_treebox_rep_partial_treebox_rep.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H H2 H5.
        forward. (* q->value=value *)
        forward. (* return *)
        entailer!.
        rewrite <- H1.
        simpl insert.
        simpl_compb; simpl_compb.
        sep_apply (treebox_rep_internal t1 k v t2 p q); auto.
        apply treebox_rep_partial_treebox_rep.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize. 
Qed.

End insert_by_Ind_Pred_Ind_Hole.

(*
Definition lookup_inv (q0: val) (t0: tree val) (x: Z): environ -> mpred :=
  EX q: val, EX t: tree val, 
  PROP(lookup nullval x t = lookup nullval x t0) 
  LOCAL(temp _q q; temp _x (Vint (Int.repr x)))
  SEP(tree_rep t q;  (tree_rep t q -* tree_rep t0 q0)).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold treebox_rep. Intros q0.
  forward. (* q=*p; *)
  apply (semax_post_ret1 nil
          (data_at Tsh (tptr t_struct_tree) q0 p0 :: tree_rep t0 q0 :: nil)).
  1: intro HH; inversion HH.
  1: unfold treebox_rep; Exists q0; entailer!.
  apply semax_frame''.
  forward_while (lookup_inv q0 t0 x).
  * (* precondition implies loop invariant *)
    Exists q0 t0. entailer!.
    apply -> wand_sepcon_adjoint. cancel.
  * (* type-check loop condition *)
    entailer!.
  * (* loop body preserves invariant *)
    destruct t; unfold tree_rep at 1; fold tree_rep. normalize.
    Intros qa qb.
    forward.
    forward_if; [ | forward_if ].
    + (* then clause: x<y *)
      forward. (* q=q<-left *)
      Exists (qa,t1). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        Exists qa qb; entailer!.
    + (* else-then clause: y<x *)
      forward. (* q=q<-right *)
      Exists (qb,t2). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        Exists qa qb; entailer!.
    + (* else-else clause: x=y *)
      assert (x=k) by omega. subst x. clear H H4 H3.
      forward. (* v=q->value *)
      forward. (* return v; *)
      unfold treebox_rep. unfold normal_ret_assert.
      entailer!.
      - rewrite <- H0. simpl.
        simpl_compb; simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply modus_ponens_wand'.
        Exists qa qb; entailer!.
  * (* after the loop *)
    forward. (* return NULL; *)
    entailer!.
    apply modus_ponens_wand.
Qed.

Lemma body_turn_left: semax_body Vprog Gprog f_turn_left turn_left_spec.
Proof.
  start_function.
  simpl.
  Intros pb pc.
  forward. (* mid=r->left *)
  forward. (* l->right=mid *)
  assert_PROP (is_pointer_or_null pb) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  forward. (* r->left=l *)
  assert_PROP (is_pointer_or_null l) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  forward. (* _l = r *)
  assert_PROP (is_pointer_or_null r) by entailer!.
  rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
  Opaque tree_rep. forward. Transparent tree_rep. (* return *)
  (* TODO: simplify the following proof *)
  Exists pc.
  entailer!.
  simpl.
  Exists pa pb.
  entailer!.
Qed.

Definition pushdown_left_inv (b_res: val) (t_res: tree val): environ -> mpred :=
  EX b: val, EX ta: tree val, EX x: Z, EX v: val, EX tb: tree val,
  PROP  () 
  LOCAL (temp _t b)
  SEP   (treebox_rep (T ta x v tb) b;
         (treebox_rep (pushdown_left ta tb) b -* treebox_rep t_res b_res)).

Lemma body_pushdown_left: semax_body Vprog Gprog f_pushdown_left pushdown_left_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ (pushdown_left_inv b (pushdown_left ta tb))
                         (pushdown_left_inv b (pushdown_left ta tb)))].
  + (* Precondition *)
    unfold pushdown_left_inv.
    Exists b ta x v tb.
    entailer!.
    eapply derives_trans; [| apply ramify_PPQQ].
    rewrite (treebox_rep_spec (T ta x v tb)).
    Exists p.
    entailer!.
  + (* Loop body *)
    unfold pushdown_left_inv.
    clear x v H H0.
    Intros b0 ta0 x vx tbc0.
    unfold treebox_rep at 1.
    Intros p0.
    forward. (* skip *)
    forward. (* p = *t; *)
      (* TODO entailer: The following should be solve automatically. satuate local does not work *)
      1: rewrite (add_andp _ _ (tree_rep_saturate_local _ _)); entailer!.
    simpl tree_rep.
    Intros pa pbc.
    forward. (* q = p->right *)
    forward_if.
    - subst.
      assert_PROP (tbc0 = (@E _)).
        1: entailer!.
      subst.
      forward. (* q=p->left *)
      forward. (* *t=q *)
      forward_call (p0, sizeof t_struct_tree). (* freeN(p, sizeof ( *p )); *)
      Focus 1. {
        entailer!.
        rewrite memory_block_data_at_ by auto.
        cancel.
      } Unfocus.
      forward. (* return *)
      apply modus_ponens_wand'.
      Exists pa.
      cancel.
    - destruct tbc0 as [| tb0 y vy tc0].
        { simpl tree_rep. normalize. }
      forward_call (ta0, x, vx, tb0, y, vy, tc0, b0, p0, pa, pbc). (* turn_left(t, p, q); *)
      Intros pc.
      forward. (* t = &q->left; *)
      Exists (field_address t_struct_tree [StructField _left] pbc) ta0 x vx tb0.
      (* TODO entailer: not to simply too much in entailer? *)
      Opaque tree_rep. entailer!. Transparent tree_rep.
        (* TODO: simplify this line *)
      apply RAMIF_PLAIN.trans'.
      apply bst_left_entail; auto.
  + forward. (* Sskip *)
    auto.
Qed.

Definition delete_inv (b0: val) (t0: tree val) (x: Z): environ -> mpred :=
  EX b: val, EX t: tree val,
  PROP()
  LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
  SEP(treebox_rep t b;  (treebox_rep (delete x t) b -* treebox_rep (delete x t0) b0)).

Lemma body_delete: semax_body Vprog Gprog f_delete delete_spec.
Proof.
  start_function.
  eapply semax_pre; [
    | apply (semax_loop _ (delete_inv b t x) (delete_inv b t x) )].
  * (* Precondition *)
    unfold delete_inv.
    Exists b t. entailer.
    apply ramify_PPQQ.
  * (* Loop body *)
    unfold delete_inv.
    Intros b1 t1.
    forward. (* Sskip *)
    unfold treebox_rep at 1. Intros p1.
    forward. (* p = *t; *)
    forward_if.
    + (* then clause *)
      subst p1.
      assert_PROP (t1= (@E _)).
        1: entailer!.
      subst t1. simpl tree_rep. rewrite !prop_true_andp by auto.
      forward. (* return; *)
      unfold treebox_rep at 1.
      apply modus_ponens_wand'.
      Exists nullval.
      simpl tree_rep.
      entailer!.
    + (* else clause *)
      destruct t1.
        { simpl tree_rep. normalize. }
      simpl tree_rep.
      Intros pa pb. clear H0.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold delete_inv.
        Exists (offset_val 8 p1) t1_1.
        entailer!.
        simpl_compb.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 8 p1)
          with (field_address t_struct_tree [StructField _left] p1)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        apply RAMIF_PLAIN.trans'.
        apply bst_left_entail; auto.
      - (* Inner if, second branch:  k<x *)
        forward. (* t=&p->right *)
        unfold delete_inv.
        Exists (offset_val 12 p1) t1_2.
        entailer!.
        simpl_compb; simpl_compb.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 12 p1)
          with (field_address t_struct_tree [StructField _right] p1)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        apply RAMIF_PLAIN.trans'.
        apply bst_right_entail; auto.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x.
        unfold_data_at 2%nat.
        gather_SEP 3 5.
        replace_SEP 0 (treebox_rep t1_1 (field_address t_struct_tree [StructField _left] p1)).
        Focus 1. {
          unfold treebox_rep; entailer!.
          Exists pa.
          rewrite field_at_data_at.
          entailer!.
        } Unfocus.
        gather_SEP 4 5.
        replace_SEP 0 (treebox_rep t1_2 (field_address t_struct_tree [StructField _right] p1)).
        Focus 1. {
          unfold treebox_rep; entailer!.
          Exists pb.
          rewrite field_at_data_at.
          entailer!.
        } Unfocus.
        forward_call (t1_1, k, v, t1_2, b1, p1).
        forward. (* return *)
        simpl_compb.
        simpl_compb.
        apply modus_ponens_wand'.
        auto.
  * (* After the loop *)
    forward.
    unfold loop2_ret_assert. apply andp_left2. normalize. 
Qed.
*)