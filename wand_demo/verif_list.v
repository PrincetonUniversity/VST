Require Import floyd.proofauto.
Require Import wand_demo.wand_frame.
Require Import wand_demo.list.
Require Import wand_demo.list_lemmas.

Module VerifHeadSwitch.

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

Definition head_head_switch_spec :=
 DECLARE _head_head_switch
  WITH sh : share, l1: val, l2: val, h1: int, t1: list int, h2: int, t2: list int
  PRE [ _l1 OF (tptr t_struct_list) , _l OF (tptr t_struct_list)]
     PROP  (writable_share sh)
     LOCAL (temp _l1 l1; temp _l2 l2)
     SEP   (listrep sh (h1 :: t1) l1; listrep sh (h2 :: t2) l2)
  POST [ tvoid ]
     PROP  ()
     LOCAL ()
     SEP   (listrep sh (h2 :: t1) l1; listrep sh (h1 :: t2) l2).

Definition Gprog : funspecs :=
  ltac:(with_library prog [ head_pointer_switch_spec; head_head_switch_spec]).

(* TODO: try use sep_apply in this proof instead of cancel, sepcon_comm. *)
Lemma body_head_pointer_switch: semax_body Vprog Gprog f_head_pointer_switch head_pointer_switch_spec.
Proof.
  start_function.
  replace_SEP 0
    (field_at sh t_struct_list [StructField _head] (Vint x) l *
      (field_at sh t_struct_list [StructField _head] (Vint y) l -* listrep sh (y :: s) l)).
    {
      entailer!.
      apply wand_frame_intro_list_head.
    }
  Intros. freeze [1] Fr.  
    forward. (* h = l -> head; *)
    forward. (* i = * p; *)
    forward. (* l -> head = i *)
    forward. (* * p = h *)
  thaw Fr.
  forward. (* return *)
  cancel.
  rewrite sepcon_comm. apply wand_frame_elim.
Qed.

Lemma body_head_head_switch: semax_body Vprog Gprog f_head_head_switch head_head_switch_spec.
Proof.
  start_function.
  replace_SEP 0
    (field_at sh t_struct_list [StructField _head] (Vint h1) l1 *
      (field_at sh t_struct_list [StructField _head] (Vint h2) l1 -* listrep sh (h2 :: t1) l1)).
    {
      entailer!.
      apply wand_frame_intro_list_head.
    }
  replace_SEP 1
    (field_at sh t_struct_list [StructField _head] (Vint h2) l2 *
      (field_at sh t_struct_list [StructField _head] (Vint h1) l2 -* listrep sh (h1 :: t2) l2)).
    {
      entailer!.
      apply wand_frame_intro_list_head.
    }
  Intros. freeze [1; 3] Fr.  
    forward. (* h1 = l1 -> head; *)
    forward. (* h2 = l2 -> head; *)
    forward. (* l1 -> head = h2; *)
    forward. (* l2 -> head = h1; *)
  thaw Fr.
  forward. (* return *)
  rewrite sepcon_assoc.
  eapply derives_trans; [apply sepcon_derives; [apply wand_frame_hor | apply derives_refl] |].
  rewrite sepcon_comm. apply wand_frame_elim.
Qed.

End VerifHeadSwitch.
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