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

End LISTS.
Arguments list_rep {V} _ _ _.

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
        data_at Tsh t_struct_Xnode (Vint (Int.repr v), q) p *
        list_rep (fun p n q => data_at Tsh t_struct_Xlist (p, n) q) r q *
        iter_sepcon2 xtree_rep tl r
  end.

Inductive YTree: Type :=
| YLeaf: YTree
| YNode: list (tree (unit * YTree) * unit) -> Z -> YTree.

Fixpoint ytree_rep (t: YTree) (p: val): mpred :=
  match t with
  | YLeaf =>
      !!(p = nullval) && emp
  | YNode ttl v =>
      EX q: val, EX r: list val,
        data_at Tsh t_struct_Ynode (Vint (Int.repr v), q) p *
        list_rep (fun r n q => data_at Tsh t_struct_Ylist (r, n) q) r q *
        iter_sepcon2 (fun tt_u_pair r =>
          EX s: tree val,
          tree_rep (fun p L R r => data_at Tsh t_struct_Ytree (p, (L, R)) r) s r *
          iter_tree_sepcon2 (fun u_t_pair s => ytree_rep (snd u_t_pair) s) (fst tt_u_pair) s) ttl r
  end.



