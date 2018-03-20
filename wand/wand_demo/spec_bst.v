Require Import VST.floyd.proofauto.
Require Import VFA.Maps.
Require Import VFA.SearchTree.
Require Import WandDemo.SearchTree_ext.
Require Import WandDemo.bst.
Require Import WandDemo.bst_lemmas.

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
  WITH p0: val, x: nat, v: val, m0: total_map val
  PRE  [ _p OF (tptr t_struct_tree), _x OF tint  ]
    PROP( Int.min_signed <= Z.of_nat x <= Int.max_signed)
    LOCAL(temp _p p0; temp _x (Vint (Int.repr (Z.of_nat x))))
    SEP (Map_rep m0 p0)
  POST [ tptr Tvoid ]
    PROP()
    LOCAL(temp ret_temp (m0 x))
    SEP (Map_rep m0 p0).

(* Turn_left is an internal function, we only need implementation correctness. *)
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

(* Pushdown_left is an internal function, we only need implementation correctness. *)
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

(* For delete, we only prove the implementation correctness for now. We could prove w.r.t. a high level specification. *)
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

