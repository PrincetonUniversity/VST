Require Import floyd.proofauto.
Require Import wand_demo.list.
Require Import wand_demo.list_lemmas.

Module VERIF_HEAD_POINTER_SWITCH.

Definition head_pointer_switch_spec :=
 DECLARE _head_pointer_switch
  WITH sh : share, l: val, p: val, x: val, s: list val, y: val
  PRE [ _l OF (tptr t_struct_list) , _p OF (tptr tint)]
     PROP  (writable_share sh)
     LOCAL (temp _l l; temp _p p)
     SEP   (listrep sh (x :: s) l; data_at sh tint y p)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (listrep sh (y :: s) l; data_at sh tint x p).

Definition Gprog : funspecs := ltac:(with_library prog [ head_pointer_switch_spec ]).

Lemma body_head_pointer_switch: semax_body Vprog Gprog f_head_pointer_switch head_pointer_switch_spec.
Proof.
  start_function.
  replace_SEP 0
    (field_at sh t_struct_list [StructField _head] x l *
      (field_at sh t_struct_list [StructField _head] y l -* listrep sh (y :: s) l)).
    {
      entailer!.
      
  forward_if (PROP (False) LOCAL () SEP ()).
*
 subst x. normalize.
 forward.
 Exists y.
 entailer!.
*

Definition append_spec (_append: ident) :=
 DECLARE _append
  WITH sh : share, contents : list int, x: val, y: val, s1: list val, s2: list val
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep sh (s1++s2) r).

Definition append_spec (_append: ident) :=
 DECLARE _append
  WITH sh : share, contents : list int, x: val, y: val, s1: list val, s2: list val
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep sh (s1++s2) r).

Definition Gprog : funspecs :=   ltac:(with_library prog [ append_spec ]).

