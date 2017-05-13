Require Import floyd.proofauto.
Require Import wand_demo.wand_frame.
Require Import wand_demo.list.
Require Import wand_demo.list_lemmas.

Module VerifHeadPointerSwitch.

Import ListHead.
  
Definition head_pointer_switch_spec :=
 DECLARE _head_pointer_switch
  WITH sh : share, l: val, p: val, x: int, s: list int, y: int
  PRE [ _l OF (tptr t_struct_list) , _p OF (tptr tint)]
     PROP  (writable_share sh)
     LOCAL (temp _l l; temp _p p)
     SEP   (listrep sh (x :: s) l; data_at sh tint (Vint y) p)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (listrep sh (y :: s) l; data_at sh tint (Vint x) p).

Definition Gprog : funspecs := ltac:(with_library prog [ head_pointer_switch_spec ]).

(* TODO: try use sep_apply in this proof instead of cancel, sepcon_comm. *)
Lemma body_head_pointer_switch: semax_body Vprog Gprog f_head_pointer_switch head_pointer_switch_spec.
Proof.
  start_function.
  replace_SEP 0
    (field_at sh t_struct_list [StructField _head] (Vint x) l *
      (field_at sh t_struct_list [StructField _head] (Vint y) l -* listrep sh (y :: s) l)).
    {
      entailer!.
      apply wf_intro_list_head.
    }
  Intros. freeze [1] Fr.  
    forward. (* h = l -> head; *)
    forward. (* i = * p; *)
    forward. (* l -> head = i *)
    forward. (* * p = h *)
  thaw Fr.
  forward. (* return *)
  cancel.
  rewrite sepcon_comm. apply wf_elim.
Qed.

End VerifHeadPointerSwitch.
(*

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

*)