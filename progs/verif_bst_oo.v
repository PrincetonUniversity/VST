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

Fixpoint tree_inb (x: key) (s: tree) : bool :=
 match s with
 | E => false
 | T a y v' b => if  x <? y then tree_inb x a
                        else if y <? x then tree_inb x b
                        else true
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

End TREES.

Arguments E {V}.
Arguments T {V} _ _ _ _.
Arguments insert {V} x v s.
Arguments tree_inb {V} x s.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Fixpoint treebox_rep (t: tree val) (b: val) : mpred :=
  match t with
  | E => data_at Tsh (tptr t_struct_tree) nullval b
  | T l x p r =>
      !! (Int.min_signed <= x <= Int.max_signed) &&
      data_at Tsh (tptr t_struct_tree) p b *
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
      treebox_rep l (field_address t_struct_tree [StructField _left] p) *
      treebox_rep r (field_address t_struct_tree [StructField _right] p)
  end.

Fixpoint key_store (s: tree val) (x: key) (q: val): Prop :=
 match s with
 | E => False
 | T a y p b => if  x <? y then key_store a x q
                        else if y <? x then key_store b x q
                        else q = field_address t_struct_tree [StructField _value] p
 end.

Definition key_store_ (s: tree val) (x: key): Prop :=
  exists v, key_store s x v.

Definition value_at (t: tree val) (v: val) (x: Z): mpred :=
  EX q: val,
  !! (key_store t x q) &&
  data_at Tsh (tptr Tvoid) v q.

(* TODO: maybe not useful *)
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
      field_at Tsh t_struct_tree [StructField _key] (Vint (Int.repr x)) p *
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

Definition subscr_spec :=
 DECLARE _subscr
  WITH b: val, x: Z, t: tree val
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _key OF tint]
    PROP(Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _key (Vint (Int.repr x)))
    SEP (treebox_rep t b)
  POST [ (tptr tvoid) ]
    EX p: val, EX q: val,
    PROP(key_store (insert x p t) x q)
    LOCAL(temp ret_temp q)
    SEP (treebox_rep (insert x p t) b;
         (!! key_store_ t x && emp) || (!! (~ key_store_ t x) && data_at Tsh (tptr tvoid) nullval q)).

(*
Definition subscr_spec1 :=
 DECLARE _subscr
  WITH b: val, x: Z, p: val, xs: Z -> Prop
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _key OF tint]
    PROP(xs x)
    LOCAL(temp _t b; temp _key (Vint (Int.repr x)))
    SEP (container_at xs b; key_store x p)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (container_at xs b; key_store x p).

Definition subscr_spec2 :=
 DECLARE _subscr
  WITH b: val, x: Z, p: val, xs: Z -> Prop
  PRE  [ _t OF (tptr (tptr t_struct_tree)), _key OF tint]
    PROP(~ xs x; Int.min_signed <= x <= Int.max_signed)
    LOCAL(temp _t b; temp _key (Vint (Int.repr x)))
    SEP (container_at xs b)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (container_at (fun x0 => xs x0 \/ x0 = x) b; key_store x p).
*)
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
(*
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
*)
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
    subscr_spec; turn_left_spec; pushdown_left_spec
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

Lemma RAMIF_Q2_trans' {X Y A : Type} {ND : NatDed A} {SL : SepLog A}:
  forall (m l: A) (g' m' l' : X -> Y -> A),
    m |-- l * (ALL p: X, ALL q: Y, l' p q -* m' p q) ->
    m * (ALL p: X, ALL q: Y, m' p q -* g' p q) |-- l * (ALL p: X, ALL q: Y, l' p q -* g' p q).
Proof.
  intros.
  eapply derives_trans; [apply sepcon_derives; [exact H | apply derives_refl] |].
  clear H.
  rewrite sepcon_assoc.
  apply sepcon_derives; auto.
  apply allp_right; intros p.
  apply allp_right; intros q.
  apply <- wand_sepcon_adjoint.
  apply (allp_left _ p), (allp_left _ q).
  apply -> wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply <- wand_sepcon_adjoint.
  apply (allp_left _ p), (allp_left _ q).
  apply -> wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply -> wand_sepcon_adjoint.
  rewrite (sepcon_comm (_ * _) _), <- sepcon_assoc.
  apply <- wand_sepcon_adjoint.
  eapply derives_trans; [apply modus_ponens_wand |].
  apply -> wand_sepcon_adjoint.
  apply modus_ponens_wand.
Qed.

Lemma if_trueb: forall {A: Type} b (a1 a2: A), b = true -> (if b then a1 else a2) = a1.
Proof. intros; subst; auto. Qed.

Lemma if_falseb: forall {A: Type} b (a1 a2: A), b = false -> (if b then a1 else a2) = a2.
Proof. intros; subst; auto. Qed.

Ltac simpl_compb :=
  match goal with
  | |- context [if Z.ltb ?x ?y then _ else _] =>
         first [ rewrite (if_trueb (Z.ltb x y)) by (apply Z.ltb_lt; omega)
               | rewrite (if_falseb (Z.ltb x y)) by (apply Z.ltb_ge; omega)]
  end.

Definition subscr_post (b0: val) (t0: tree val) (x: Z) (p: val) (q: val) :=
  !! key_store (insert x p t0) x q &&
  treebox_rep (insert x p t0) b0 *
  (if tree_inb x t0 then emp else data_at Tsh (tptr tvoid) nullval q).

Definition subscr_inv (b0: val) (t0: tree val) (x: Z): environ -> mpred :=
  EX b: val, EX t: tree val, 
  PROP() 
  LOCAL(temp _t b; temp _key (Vint (Int.repr x)))
  SEP(treebox_rep t b;
      ALL p: val, ALL q: val, subscr_post b t x p q -* subscr_post b0 t0 x p q).

Axiom tree_inb_true_iff: forall x (t: tree val), tree_inb x t = true <-> key_store_ t x.
Axiom tree_inb_false_iff: forall x (t: tree val), tree_inb x t = false <-> ~ key_store_ t x.

Lemma body_subscr: semax_body Vprog Gprog f_subscr subscr_spec.
Proof.
  start_function.
  apply semax_post'' with
     (EX p: val, EX q: val,
                       PROP ( )
                       LOCAL (temp ret_temp q)
                       SEP (subscr_post b t x p q)).
 reflexivity.
 { 
  Intros p q; Exists p q.
  unfold subscr_post.
  destruct (tree_inb x t) eqn:?.
  apply tree_inb_true_iff in  Heqb0. entailer!.  apply orp_right1. auto.
  apply tree_inb_false_iff in  Heqb0. entailer!. apply orp_right2. entailer!.
 }
  rename H into Range_x.
  eapply semax_pre; [
    | apply (semax_loop _ (subscr_inv b t x) (subscr_inv b t x))].
  * (* Precondition *)
    unfold subscr_inv.
    Exists b t.
    entailer!.
    apply allp_right; intros p.
    apply allp_right; intros q.
    apply wand_sepcon_adjoint; entailer!.
  * (* Loop body *)
    (* TODO: why this skip is here? *)
    forward. (* Sskip *)
    unfold subscr_inv.
    Intros b1 t1.
    destruct t1; simpl treebox_rep at 1; normalize.
    + forward. (* p = *t; *)
      forward_if; [clear H | inversion H]. (* then clause *)
      forward_call (sizeof t_struct_tree).
        1: simpl; repable_signed.
      Intros p1.
      rewrite memory_block_data_at_ by auto.
      forward. (* p->key=x; *)
      simpl.
      forward. (* p->value=NULL; *)
      forward. (* p->left=NULL; *)
      forward. (* p->right=NULL; *)
      forward. (* *t = p; *)
      forward. (* return (&p->value); *)
      Exists p1 (offset_val 4 p1).
      rewrite (sepcon_comm (_ * _)); apply wand_sepcon_adjoint.
      apply (allp_left _ p1), (allp_left _ (offset_val 4 p1)).
      apply wand_sepcon_adjoint; rewrite <- (sepcon_comm (_ * _)).
      entailer!.
      apply modus_ponens_wand'.
      unfold subscr_post.
      simpl.
      replace (offset_val 4 p1)
        with (field_address t_struct_tree [StructField _value] p1)
        by (unfold field_address; simpl;
            rewrite if_true by auto with field_compatible; auto).
      simpl_compb. simpl_compb.
      unfold_field_at 1%nat.
      rewrite (field_at_data_at _ t_struct_tree [StructField _value]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _left]).
      rewrite (field_at_data_at _ t_struct_tree [StructField _right]).
      entailer!.
    + forward. (* p = *t; *)
      forward_if. (* else clause *)
       (* TODO: better automation for field_compatible. *)
        1: admit.
      (* TODO: better automation for field_compatible. *)
        1: admit.
      forward. (* y=p->key; *)
      forward_if; [ | forward_if ].
      - (* Inner if, then clause: x<k *)
        forward. (* t=&p->left *)
        unfold subscr_inv.
        Exists (offset_val 8 v) t1_1.
        entailer!.
        apply RAMIF_Q2_trans'.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 8 v)
          with (field_address t_struct_tree [StructField _left] v)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        entailer!.
        apply allp_right; intros p.
        apply allp_right; intros q.
        apply -> wand_sepcon_adjoint.
        unfold subscr_post.
        simpl.
        simpl_compb.
        simpl_compb.
        simpl.
        simpl_compb.
        entailer!.
      - (* Inner if, second branch:  k<x *)
        forward. (* t=&p->right *)
        unfold subscr_inv.
        Exists (offset_val 12 v) t1_2.
        entailer!.
        apply RAMIF_Q2_trans'.
        (* TODO: SIMPLY THIS LINE *)
        replace (offset_val 12 v)
          with (field_address t_struct_tree [StructField _right] v)
          by (unfold field_address; simpl;
              rewrite if_true by auto with field_compatible; auto).
        entailer!.
        apply allp_right; intros p.
        apply allp_right; intros q.
        apply -> wand_sepcon_adjoint.
        unfold subscr_post.
        simpl.
        simpl_compb.
        simpl_compb.
        simpl.
        simpl_compb.
        simpl_compb.
        simpl_compb.
        simpl_compb.
        entailer!.
      - (* Inner if, third branch: x=k *)
        assert (x=k) by omega.
        subst x. clear H1 H2.
        forward. (* return (&p->value) *)
        Exists v (offset_val 4 v).
        entailer!.
        rewrite (sepcon_comm (_ * _ * _ * _)); apply wand_sepcon_adjoint.
        apply (allp_left _ v), (allp_left _ (offset_val 4 v)).
        apply wand_sepcon_adjoint; rewrite <- (sepcon_comm (_ * _ * _ * _)).
        apply modus_ponens_wand'.
        unfold subscr_post.
        simpl.
        simpl_compb.
        simpl_compb.
        simpl_compb.
        simpl_compb.
        simpl.
        simpl_compb.
        simpl_compb.
        entailer!.
        unfold field_address; simpl.
        rewrite if_true; auto.
        rewrite field_compatible_cons in H3 |- *.
        simpl in H3 |- *.
        split.
        1: right; left; auto.
        tauto.
  * (* After the loop *)
    forward.
    simpl loop2_ret_assert. apply andp_left2. auto.
Admitted.
(*
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