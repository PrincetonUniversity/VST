Require Import VST.floyd.proofauto.
Require Import VST.progs.tree.
Require Import VST.msl.iter_sepcon.

Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_Xnode := Tstruct _Xnode noattr.
Definition t_struct_Xlist := Tstruct _XList noattr.
Definition t_struct_Ynode := Tstruct _Ynode noattr.
Definition t_struct_Ylist := Tstruct _YList noattr.
Definition t_struct_Ytree := Tstruct _BinaryTree noattr.

Section LISTS.
Variable V: Type.

Variable list_cell: V -> val -> val -> mpred.

Fixpoint list_rep (l: list V) (x: val) : mpred :=
 match l with
 | h::hs => 
    EX y:val, list_cell h y x * list_rep hs y
 | nil => 
    !! (x = nullval) && emp
 end.

Lemma list_rep_valid_pointer:
  (forall v q p, list_cell v q p |-- valid_pointer p) ->
  forall l p, list_rep l p |-- valid_pointer p.
Proof.
  intros.
  destruct l; simpl; normalize; auto with valid_pointer.
Qed.

Lemma list_rep_local_facts:
  (forall v q p, list_cell v q p |-- !! (isptr p)) ->
  forall l p, list_rep l p |-- !! (is_pointer_or_null p  /\ (p=nullval <-> l=nil)).
Proof.
  intros.
  destruct l; simpl; normalize; entailer!.
  + split; auto.
  + split; intros; try congruence.
    subst; inv Pp.
Qed.

End LISTS.
Arguments list_rep {V} _ _ _.
Arguments list_rep_valid_pointer {V} _ _ _ _ _ _.

Section TREES.
Variable V : Type.

Inductive tree : Type :=
 | E : tree
 | T: tree -> V -> tree -> tree.

Variable tree_cell: V -> val -> val -> val -> mpred.

Fixpoint tree_rep (t: tree) (p: val) : mpred :=
 match t with
 | E => !!(p=nullval) && emp
 | T a v b =>
    EX pa:val, EX pb:val,
    tree_cell v pa pb p *
    tree_rep a pa * tree_rep b pb
 end.

End TREES.
Arguments E {V}.
Arguments T {V} _ _ _.
Arguments tree_rep {V} _ _ _.

Definition map_tree {V1 V2: Type} (f: V1 -> V2): tree V1 -> tree V2 :=
  fix map_tree (t: tree V1) :=
    match t with
    | E => E
    | T t1 x t2 => T (map_tree t1) (f x) (map_tree t2)
    end.

Section IterTreeSepCon2.

  Context {A : Type}.
  Context {B1 B2 : Type}.
  Context {ND : NatDed A}.
  Context {SL : SepLog A}.
  Context {ClS: ClassicalSep A}.
  Context {CoSL: CorableSepLog A}.
  Context (p : B1 -> B2 -> A).

Fixpoint iter_tree_sepcon2 (t1 : tree B1) : tree B2 -> A :=
    match t1 with
    | E => fun t2 =>
       match t2 with
       | E => emp
       | _ => FF
       end
    | T xa x xb => fun t2 =>
       match t2 with
       | E => FF
       | T ya y yb => p x y * iter_tree_sepcon2 xa ya * iter_tree_sepcon2 xb yb
       end
  end.

End IterTreeSepCon2.

Inductive XTree: Type :=
| XLeaf: XTree
| XNode: list XTree -> Z -> XTree.

Fixpoint xtree_rep (t: XTree) (p: val): mpred :=
  match t with
  | XLeaf =>
      !!(p = nullval) && emp
  | XNode tl v =>
      EX q: val, EX r: list val,
        data_at Tsh t_struct_Xnode (q, Vint (Int.repr v)) p *
        list_rep (fun (p: val) (n: val) (q: val) => data_at Tsh t_struct_Xlist (p, n) q) r q *
        iter_sepcon2 xtree_rep tl r
  end.

Lemma xtree_rep_valid_pointer:
  forall t p, xtree_rep t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve xtree_rep_valid_pointer: valid_pointer.

Lemma list_rep_Xlist_valid_pointer:
  forall (r: list val) (q: val),
    list_rep (fun (p: val) (n: val) (q: val) => data_at Tsh t_struct_Xlist (p, n) q) r q |-- valid_pointer q.
Proof.
  intros.
  apply list_rep_valid_pointer.
  intros.
  auto with valid_pointer.
Qed.
Hint Resolve list_rep_Xlist_valid_pointer: valid_pointer.

Lemma list_rep_Xlist_local_facts:
  forall (r: list val) (q: val),
    list_rep (fun (p: val) (n: val) (q: val) => data_at Tsh t_struct_Xlist (p, n) q) r q |-- !! (is_pointer_or_null q  /\ (q=nullval <-> r=nil)).
Proof.
  intros.
  apply list_rep_local_facts.
  intros.
  entailer!.
Qed.
Hint Resolve list_rep_Xlist_local_facts: saturate_local.

Lemma xtree_rep_nullval: forall t,
  xtree_rep t nullval |-- !! (t = XLeaf).
Proof.
  intros.
  destruct t; [entailer! |].
  simpl xtree_rep.
  Intros q r. entailer!.
Qed.
Hint Resolve xtree_rep_nullval: saturate_local.

Inductive YTree: Type :=
| YLeaf: YTree
| YNode: list (tree (unit * YTree) * unit) -> Z -> YTree.

Fixpoint ytree_rep (t: YTree) (p: val): mpred :=
  match t with
  | YLeaf =>
      !!(p = nullval) && emp
  | YNode ttl v =>
      let rep1 (t: unit * YTree) p := ytree_rep (snd t) p in
      let rep2 (t: tree (unit * YTree) * unit) p :=
            EX s: tree val,
              tree_rep (fun q L R p => data_at Tsh t_struct_Ytree (q, (L, R)) p) s p *
              iter_tree_sepcon2 rep1 (fst t) s in
      let rep3 (t: list (tree (unit * YTree) * unit)) p :=
            EX r: list val,
              list_rep (fun q n p => data_at Tsh t_struct_Ylist (q, n) p) r p *
              iter_sepcon2 rep2 t r in
      EX q: val, 
        data_at Tsh t_struct_Ynode (q, Vint (Int.repr v)) p * rep3 ttl q
  end.

Definition t_ytree_rep (t: tree (unit * YTree)) (p: val): mpred :=
  EX s: tree val,
    tree_rep (fun q L R p => data_at Tsh t_struct_Ytree (q, (L, R)) p) s p *
    iter_tree_sepcon2 (fun t p => ytree_rep (snd t) p) t s.

Definition lt_ytree_rep (t: list (tree (unit * YTree) * unit)) (p: val): mpred :=
  EX r: list val,
    list_rep (fun q n p => data_at Tsh t_struct_Ylist (q, n) p) r p *
    iter_sepcon2 (fun t p => t_ytree_rep (fst t) p) t r.

Theorem ytree_rep_spec: forall t p,
  ytree_rep t p =
  match t with
  | YLeaf =>
      !!(p = nullval) && emp
  | YNode ttl v =>
      EX q: val, 
        data_at Tsh t_struct_Ynode (q, Vint (Int.repr v)) p * lt_ytree_rep ttl q
  end.
Proof.
  intros.
  induction t; auto.
Qed.

Lemma ytree_rep_valid_pointer:
  forall t p, ytree_rep t p |-- valid_pointer p.
Proof.
intros.
destruct t; simpl; normalize; auto with valid_pointer.
Qed.
Hint Resolve ytree_rep_valid_pointer: valid_pointer.

Module Alternative.

Fixpoint ytree_rep (t: YTree) (p: val): mpred :=
  match t with
  | YLeaf =>
      !!(p = nullval) && emp
  | YNode ttl v =>
      EX q: val, EX r: list val,
        data_at Tsh t_struct_Ynode (q, Vint (Int.repr v)) p *
        list_rep (fun r n q => data_at Tsh t_struct_Ylist (r, n) q) r q *
        iter_sepcon2 (fun tt_u_pair r =>
          EX s: tree val,
          tree_rep (fun p L R r => data_at Tsh t_struct_Ytree (p, (L, R)) r) s r *
          iter_tree_sepcon2 (fun u_t_pair s => ytree_rep (snd u_t_pair) s) (fst tt_u_pair) s) ttl r
  end.

End Alternative.

Fixpoint x_add1 (t: XTree): XTree :=
  match t with
  | XLeaf =>
      XLeaf
  | XNode tl v =>
      XNode (map x_add1 tl) (v + 1)
  end.

Definition Xnode_add_spec :=
 DECLARE _Xnode_add
  WITH p: val, t: XTree
  PRE  [ _p OF (tptr t_struct_Xnode) ]
    PROP  ()
    LOCAL (temp _p p)
    SEP (xtree_rep t p)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (xtree_rep (x_add1 t) p).

Fixpoint y_add1 (t: YTree): YTree :=
  match t with
  | YLeaf =>
      YLeaf
  | YNode tl v =>
      let map1 := fun u_t_pair => (tt, y_add1 (snd u_t_pair)) in
      let map2 := fun tt_u_pair => (map_tree map1 (fst tt_u_pair), tt) in
      let map3 := fun tl => map map2 tl in
      YNode (map3 tl) (v + 1)
  end.

Definition ty_add1 (t: tree (unit * YTree)) :=
  map_tree (fun t => (tt, y_add1 (snd t))) t.

Definition lty_add1 (t: list (tree (unit * YTree) * unit)) :=
  map (fun t => (ty_add1 (fst t), tt)) t.

Theorem y_add1_spec: forall t,
  y_add1 t = 
  match t with
  | YLeaf =>
      YLeaf
  | YNode tl v =>
      YNode (lty_add1 tl) (v + 1)
  end.
Proof.
  intros.
  induction t; auto.
Qed.

Definition Ynode_add_spec :=
 DECLARE _Ynode_add
  WITH p: val, t: YTree
  PRE  [ _p OF (tptr t_struct_Ynode) ]
    PROP  ()
    LOCAL (temp _p p)
    SEP (ytree_rep t p)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (ytree_rep (y_add1 t) p).

Definition YTree_add_spec :=
 DECLARE _YTree_add
  WITH p: val, t: tree (unit * YTree)
  PRE  [ _p OF (tptr t_struct_Ytree) ]
    PROP  ()
    LOCAL (temp _p p)
    SEP (t_ytree_rep t p)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (t_ytree_rep (ty_add1 t) p).

Definition YList_add_spec :=
 DECLARE _YList_add
  WITH p: val, t: list (tree (unit * YTree) * unit)
  PRE  [ _p OF (tptr t_struct_Ylist) ]
    PROP  ()
    LOCAL (temp _p p)
    SEP (lt_ytree_rep t p)
  POST [ Tvoid ] 
    PROP()
    LOCAL()
    SEP (lt_ytree_rep (lty_add1 t) p).

Definition main_spec :=
 DECLARE _main
  WITH gv : globals
  PRE  [] main_pre prog nil gv
  POST [ tint ]
     PROP() LOCAL () SEP(TT).

Definition Gprog : funspecs :=
  ltac:(with_library prog
    [Xnode_add_spec; Ynode_add_spec; YList_add_spec; YTree_add_spec; main_spec]).

Lemma body_Xnode_add: semax_body Vprog Gprog f_Xnode_add Xnode_add_spec.
Proof.
  start_function.
  unfold MORE_COMMANDS, abbreviate.
  forward_if.
  {
    forward.
    entailer!.
    simpl.
    auto.
  }
  unfold Sfor.
  destruct t as [| tl v].
  {
    simpl.
    Intros.
    contradiction.
  }
  simpl.
  Intros q r.
  forward.
  forward.
  unfold Sfor.
  forward.
Abort.