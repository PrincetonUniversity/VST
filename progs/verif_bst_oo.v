Require Import floyd.proofauto.
Require Import progs.bst_oo.

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

(* insert if it is new *)
Fixpoint insert (x: key) (v: V) (s: tree) : tree :=
 match s with 
 | E => T E x v E
 | T a y v' b => if  x <? y then T (insert x v a) y v' b
                        else if y <? x then T a y v' (insert x v b)
                        else T a x v' b
 end.

Fixpoint pushdown_left (a: tree) (bc: tree) : tree :=
 match bc with
 | E => a
 | T b y vy c => T (pushdown_left a b) y vy c
 end.

Fixpoint delete (x: key) (s: tree) : tree :=
 match s with
 | E => E
 | T a y v' b => if  x <? y then T (delete x a) y v' b
                        else if y <? x then T a y v' (delete x b)
                        else pushdown_left a b
 end.

Fixpoint tree_in (x: key) (s: tree) : Prop :=
 match s with 
 | E => False
 | T a y _ b => tree_in x a \/ x = y \/ tree_in x b
 end.

Definition has_keys (s: tree) (xs: key -> Prop): Prop :=
  forall x, tree_in x s <-> xs x.

End TREES.

Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.
Arguments tree_in {V} x s.
Arguments has_keys {V} s xs.

Parameter Ash: share.
Parameter Bsh: share.
Axiom Ash_readable: readable_share Ash.
Axiom Bsh_readable: readable_share Bsh.
Axiom ABsh_Tsh: sepalg.join Ash Bsh Tsh.

Fixpoint treebox_rep (t: tree val) (b: val) : mpred :=
  match t with
  | E => data_at Tsh (tptr t_struct_tree) nullval b
  | T l x p r =>
      !! (Int.min_signed <= x <= Int.max_signed) &&
      data_at Tsh (tptr t_struct_tree) p b *
      field_at Ash t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.

Definition key_store (x: Z) (p: val): mpred :=
  EX q: val,
    !! (p = field_address t_struct_tree [StructField _value] q) &&
    field_at Bsh t_struct_tree [StructField _key] (Vint (Int.repr x)) q.

Definition value_at (v: val) (x: Z): mpred :=
  EX p: val, key_store x p * data_at Tsh (tptr Tvoid) v p.

Definition container_at (xs: Z -> Prop) (b: val): mpred :=
  EX t: tree val, !! (has_keys t xs) && treebox_rep t b.

Lemma treebox_rep_spec: forall (t: tree val) (b: val),
  treebox_rep t b =
  data_at Tsh (tptr t_struct_tree)
    match t return val with
    | E => nullval
    | T _ _ p _ => p
    end b *
  match t with
  | E => emp
  | T l x p r =>
      !! (Int.min_signed <= x <= Int.max_signed) &&
      field_at Ash t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.
Proof.
  intros.
  destruct t; simpl; apply pred_ext; entailer!.
Qed.

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

Definition subscr_spec1 :=
 DECLARE _subscr
  WITH b: val, x: Z, p: val, xs: Z -> Prop
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP(xs x)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (container_at xs b; key_store x p)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (container_at xs b; key_store x p).

Definition subscr_spec2 :=
 DECLARE _subscr
  WITH b: val, x: Z, p: val, xs: Z -> Prop
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP(~ xs x; Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (container_at xs b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (container_at (fun x0 => xs x0 \/ x0 = x) b; key_store x p).

Definition turn_left_spec :=
 DECLARE _turn_left
  WITH ta: tree val, x: Z, tb: tree val, y: Z, tc: tree val, b: val, l: val, r: val
  PRE  [ __l OF (tptr (tptr (Tstruct _tree noattr))),
        _l OF (tptr (Tstruct _tree noattr)),
        _r OF (tptr (Tstruct _tree noattr))]
    PROP()
    LOCAL(temp __l b; temp _l l; temp _r r)
    SEP (treebox_rep (T ta x l (T tb y r tc)) b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (T (T ta x l tb) y r tc) b).

Definition pushdown_left_spec :=
 DECLARE _pushdown_left
  WITH ta: tree val, x: Z, tb: tree val, b: val, p: val
  PRE  [ _t OF (tptr (tptr (Tstruct _tree noattr)))]
    PROP()
    LOCAL(temp _t b)
    SEP (treebox_rep (T ta x p tb) b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (treebox_rep (pushdown_left ta tb) b).

Definition delete_spec1 :=
 DECLARE _delete
  WITH b: val, x: Z, xs: Z -> Prop
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP(xs x)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (container_at xs b; value_at Vundef x)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (container_at (fun x0 => xs x0 /\ x0 <> x) b).

Definition delete_spec2 :=
 DECLARE _delete
  WITH b: val, x: Z, xs: Z -> Prop
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _x OF tint]
    PROP(~ xs x)
    LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
    SEP (container_at xs b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (container_at xs b).
(*
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
*)
Definition Gprog : funspecs := 
    ltac:(with_library prog [
    mallocN_spec; freeN_spec; treebox_new_spec; 
    subscr_spec1; turn_left_spec; pushdown_left_spec
  ]).

Lemma treebox_rep_saturate_local:
   forall t b, treebox_rep t b |-- !! field_compatible (tptr t_struct_tree) [] b.
Proof.
intros.
destruct t.
+ simpl.
  entailer!.
+ simpl.
  entailer!.
Qed.

Hint Resolve treebox_rep_saturate_local: saturate_local.

(*
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

*)
Lemma modus_ponens_wand' {A}{ND: NatDed A}{SL: SepLog A}:
  forall P Q R: A, P |-- Q -> P * (Q -* R) |-- R.
Proof.
  intros.
  eapply derives_trans; [| apply modus_ponens_wand].
  apply sepcon_derives; [| apply derives_refl].
  auto.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb := first [ rewrite if_trueb by (apply Z.ltb_lt; omega)
                          | rewrite if_falseb by (apply Z.ltb_ge; omega)].

Definition subscr1_inv (b0: val) (t0: tree val) (x: Z) (p: val): environ -> mpred :=
  EX b: val, EX t: tree val, 
  PROP(tree_in x t) 
  LOCAL(temp _t b; temp _x (Vint (Int.repr x)))
  SEP(treebox_rep t b; key_store x p; (treebox_rep t b -* treebox_rep t0 b0)).

Lemma body_subscr1: semax_body Vprog Gprog f_subscr subscr_spec1.
Proof.
  start_function.
  unfold container_at.
  Intros t.
  rewrite <- (H0 x) in H.
  eapply semax_pre; [
    | apply (semax_loop _ (subscr1_inv b t x p) (subscr1_inv b t x p))].
  * (* Precondition *)
    unfold subscr1_inv.
    Exists b t.
    (* TODO entailer: entailer! fails *)
    admit.
    (* apply ramify_PPQQ. *)
  * (* Loop body *)
    forward. (* Sskip *)
    unfold subscr1_inv.
    Intros b1 t1.
    (* TODO: without this "set", "rewrite ... at 1" is super slow. *)
    set (tb := treebox_rep t1 b1) at 2.
    rewrite (treebox_rep_spec t1 b1).
    subst tb.
    normalize.
    forward. (* p = *t; *)
Abort.
(*
    destruct t1; entailer!.
    forward_if.
    + (* then clause *)
      subst p1.
      forward_call (sizeof t_struct_tree).
        1: simpl; repable_signed.
      Intros p'.
      rewrite memory_block_data_at_ by auto.
      forward. (* p->key=x; *)
      simpl.
      forward. (* p->value=value; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)
      assert_PROP (t1= (@E _)).
        1: entailer!.
      subst t1. simpl tree_rep. rewrite !prop_true_andp by auto.
      rewrite is_pointer_or_null_force_val_sem_cast_neutral by auto.
      forward. (* *t = p; *)
      forward. (* return; *)
      apply modus_ponens_wand'.
      apply treebox_rep_leaf; auto.
    + (* else clause *)
      destruct t1.
        { simpl tree_rep. normalize. contradiction H1; auto. }
      simpl tree_rep.
      Intros pa pb. clear H1.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold insert_inv.
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
        unfold insert_inv.
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
        subst x. clear H H1 H4.
        forward. (* p->value=value *)
        forward. (* return *)
        (* TODO: SIMPLY THIS LINE *)
        simpl_compb.
        simpl_compb.
        apply modus_ponens_wand'.
        unfold treebox_rep. Exists p1.
        simpl tree_rep. Exists pa pb. entailer!.
  * (* After the loop *)
    forward.
    simpl loop2_ret_assert. apply andp_left2. auto.
Qed.

Definition lookup_inv (b0 p0: val) (t0: tree val) (x: Z): environ -> mpred :=
  EX p: val, EX t: tree val, 
  PROP(lookup nullval x t = lookup nullval x t0) 
  LOCAL(temp _p p; temp _x (Vint (Int.repr x)))
  SEP(tree_rep t p;  (tree_rep t p -* tree_rep t0 p0)).

Lemma body_lookup: semax_body Vprog Gprog f_lookup lookup_spec.
Proof.
  start_function.
  unfold treebox_rep. Intros p.
  forward. (* p=*t; *)
  apply (semax_post''
                      (PROP ( )
                       LOCAL (temp ret_temp (lookup nullval x t))
                       SEP (data_at Tsh (tptr t_struct_tree) p b; tree_rep t p))).
  1: unfold treebox_rep; Exists p.
     (* TODO: let entailer work here. *)
     apply derives_refl'. f_equal. f_equal.
     unfold SEPx; simpl. extensionality rho. symmetry; apply sepcon_assoc.
  apply semax_frame''.
  forward_while (lookup_inv b p t x).
  * (* precondition implies loop invariant *)
    Exists p t. entailer!.
    apply -> wand_sepcon_adjoint. cancel.
  * (* type-check loop condition *)
    entailer!.
  * (* loop body preserves invariant *)
    destruct t0; unfold tree_rep at 1; fold tree_rep. normalize.
    contradiction HRE; auto.
    Intros pa pb.
    forward.
    forward_if; [ | forward_if ].
    + (* then clause: x<y *)
      forward. (* p=p<-left *)
      Exists (pa,t0_1). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        Exists pa pb; entailer!.
    + (* else-then clause: y<x *)
      forward. (* p=p<-right *)
      Exists (pb,t0_2). unfold fst,snd.
      entailer!.
      - rewrite <- H0; simpl.
        simpl_compb; simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply RAMIF_PLAIN.trans''.
        apply -> wand_sepcon_adjoint.
        Exists pa pb; entailer!.
    + (* else-else clause: x=y *)
      assert (x=k) by omega. subst x. clear H H4 H5.
      forward. (* v=p->value *)
      forward. (* return v; *)
      unfold treebox_rep. unfold normal_ret_assert.
      entailer!.
      - rewrite <- H0. simpl.
        simpl_compb; simpl_compb; auto.
      - (* TODO: merge the following 2 lines *)
        apply modus_ponens_wand'.
        Exists pa pb; entailer!.
  * (* after the loop *)
    forward. (* return NULL; *)
    entailer!.
    apply modus_ponens_wand.
Qed.
*)
(*
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
      (* TODO: The following should be solve automatically. satuate local does not work *)
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
        { simpl tree_rep. normalize. contradiction H1; auto. }
      forward_call (ta0, x, vx, tb0, y, vy, tc0, b0, p0, pa, pbc). (* turn_left(t, p, q); *)
      Intros pc.
      forward. (* t = &q->left; *)
      Exists (field_address t_struct_tree [StructField _left] pbc) ta0 x vx tb0.
      (* TODO: not to simply to much in entailer? *)
      Opaque tree_rep. entailer!. Transparent tree_rep.
        (* TODO: simplify this line *)
        1: unfold field_address; simpl; rewrite if_true by auto with field_compatible; auto.
      apply RAMIF_PLAIN.trans'.
      apply bst_left_entail; auto.
  + forward. (* Sskip *)
    (* TODO: entailer! does not work here. *)
    unfold loop2_ret_assert.
    apply andp_left2, derives_refl.
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
  + destruct t; simpl tree_rep.
      1: Intros. contradiction.
    Intros pa pb.
    forward.
    forward.
    forward_call (p, sizeof t_struct_tree).
    Focus 1. {
      entailer!.
      rewrite memory_block_data_at_ by auto.
      cancel.
    } Unfocus.
    forward_call (t1,pa).
    forward_call (t2,pb).
    entailer!.
  + forward.
    subst.
    entailer!.
    simpl; normalize.
  + forward.
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

*)