Require Import VST.progs.conclib.
Require Import VST.progs.bst_conc.
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.



Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition t_struct_tree := Tstruct _tree noattr.
Definition t_struct_tree_t := Tstruct _tree_t noattr.

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
Arguments lookup {V} default x t.
Arguments pushdown_left {V} a bc.
Arguments delete {V} x s.

Eval hnf in reptype (nested_field_type t_struct_tree_t [StructField _lock]).




Definition ltree tl lsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p *
   lock_inv lsh lock (tl (p, lock))) .


Fixpoint node_rep tl lsh (t: tree val) (p: val) : mpred := (*tree strored in p correctly, see struct tree, representation in memory*)
 match t with
 | E => !!(p=nullval) && emp
 | T a x v b => !! (Int.min_signed <= x <= Int.max_signed /\ tc_val (tptr Tvoid) v) &&
    EX pa:val, EX pb:val, EX locka : val, EX lockb : val,
    data_at Tsh t_struct_tree (Vint (Int.repr x),(v,(pa,pb))) p *
    ltree tl lsh pa locka  * ltree tl lsh pb lockb 
 end.
 
 Definition t_lock_pred tl lsh t p lock :=
  EX tp : val, (data_at Tsh (tptr t_struct_tree) tp p * node_rep tl lsh t tp *
    malloc_token Tsh (t_struct_tree_t) p *
   malloc_token Tsh (tlock) lock).
   
Definition t_lock_pred' tl lsh p lock  := EX t : tree val, t_lock_pred tl lsh t p lock.

Definition t_lock_pred_uncurry lsh (tl : ((val * val) -> mpred)) := fun '(p, lock) => 
  t_lock_pred' tl lsh p lock.

Definition t_lock_pred'' lsh :=  HORec (t_lock_pred_uncurry lsh).

Definition t_lock_pred''' lsh p lock := t_lock_pred'' lsh (p,lock).


Definition ltree_final lsh p lock :=
  !!(field_compatible t_struct_tree_t nil p) &&
  (field_at lsh t_struct_tree_t [StructField _lock] lock p *
   lock_inv lsh lock (t_lock_pred''' lsh p lock)).



Theorem t_lock_pred_def : forall lsh p lock, 
  t_lock_pred''' lsh p lock = t_lock_pred' (t_lock_pred'' lsh) lsh p lock.
Proof.
Admitted.
   


Definition treebox_rep (t: tree val) (b: val) :=
 EX p: val, data_at Tsh (tptr t_struct_tree_t) p b.
 
 
(*maybe I should add the treebox_rep in the ltree definition *)
Definition insert_spec' :=
  WITH sh : share, p : val, lock : val,
       b: val, x: Z, v: val, t: tree val
  PRE [  _t OF (tptr (tptr t_struct_tree_t)), _x OF tint,
        _value OF (tptr Tvoid)  ]
   PROP (readable_share sh; Int.min_signed <= x <= Int.max_signed; is_pointer_or_null v)
   LOCAL (temp _t b; temp _x (Vint (Int.repr x)); temp _value v)
   SEP (treebox_rep t b; ltree_final sh p lock)
  POST [ Tvoid ]
   PROP ()
   LOCAL ()
   SEP (treebox_rep (insert x v t) b; ltree_final sh p lock).
Definition insert_spec prog := DECLARE (ext_link_prog prog "insert") insert_spec'.







   
   