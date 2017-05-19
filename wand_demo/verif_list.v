Require Import floyd.proofauto.
Require Import wand_demo.wand_frame.
Require Import wand_demo.wand_frame_tactic.
Require Import wand_demo.wandQ_frame.
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
  apply_wand_frame_elim; cancel.
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
  apply_wand_frame_elim; cancel.
Qed.

End VerifHeadSwitch.

Module VerifAppend.

Definition append_spec (_append: ident) :=
 DECLARE _append
  WITH sh : share, contents : list int, x: val, y: val, s1: list int, s2: list int
  PRE [ _x OF (tptr t_struct_list) , _y OF (tptr t_struct_list)]
     PROP(writable_share sh)
     LOCAL (temp _x x; temp _y y)
     SEP (listrep sh s1 x; listrep sh s2 y)
  POST [ tptr t_struct_list ]
    EX r: val,
     PROP()
     LOCAL(temp ret_temp r)
     SEP (listrep sh (s1++s2) r).

Module VerifAppend1.

Import ListLib.

Definition append1_spec := append_spec _append1.

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append1_spec ]).

Module ProofByNoWand.

Import LsegRecursive.

Lemma body_append1: semax_body Vprog Gprog f_append1 append1_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  * rewrite (listrep_null _ _ x) by auto. normalize.
    forward. (* return; *)
    Exists y.
    entailer!.
  * forward. (* t = x; *)
    rewrite (listrep_nonnull _ _ x) by auto.
    Intros v s1' u.
    forward. (* u = t -> tail; *)
    forward_while
      ( EX s1a: list int, EX b: int, EX s1c: list int, EX t: val, EX u: val,
            PROP (s1 = s1a ++ b :: s1c)
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (lseg sh s1a x t;
                 field_at sh t_struct_list [StructField _head] (Vint b) t;
                 field_at sh t_struct_list [StructField _tail] u t;
                 listrep sh s1c u;
                 listrep sh s2 y))%assert.
+ (* current assertion implies loop invariant *)
   Exists (@nil int) v s1' x u.
   subst s1. entailer!. unfold lseg; simpl; entailer!.
+ (* loop test is safe to execute *)
   entailer!.
+ (* loop body preserves invariant *)
  clear v H0.
  rewrite (listrep_nonnull _ _ u0) by auto.
  Intros c s1d z.
  forward. (* t = u; *)
   forward. (* u = t -> tail; *)
   Exists ((s1a ++ b :: nil),c,s1d,u0,z). unfold fst, snd.
   simpl app.
   entailer.
   apply andp_right; [apply prop_right; apply (app_assoc s1a [b] (c :: s1d)) |].
   sep_apply (singleton_lseg' sh b c t u0); auto.
   sep_apply (lseg_lseg sh s1a [b] c x t u0); auto.
   cancel.
+ (* after the loop *)
   clear v s1' H0.
   forward. (* t -> tail = y; *)
   forward. (* return x; *)
   Exists x.
   rewrite (listrep_null _ s1c) by auto.
   entailer.
   simpl app.
   sep_apply (singleton_lseg sh s2 b t y); auto.
   sep_apply (list_lseg sh [b] s2 t y).
   rewrite <- app_assoc.
   sep_apply (list_lseg sh s1a ([b] ++ s2) x t).
   auto.
Qed.

End ProofByNoWand.

Module ProofByWandFrame1.

Import LsegWandFrame.
  
Lemma body_append1: semax_body Vprog Gprog f_append1 append1_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  * rewrite (listrep_null _ _ x) by auto. normalize.
    forward. (* return; *)
    Exists y.
    entailer!.
  * forward. (* t = x; *)
    rewrite (listrep_nonnull _ _ x) by auto.
    Intros v s1' u.
    forward. (* u = t -> tail; *)
    forward_while
      ( EX a: int, EX s1b: list int, EX t: val, EX u: val,
            PROP ()
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (listrep sh (a::s1b++s2) t -* listrep sh (s1++s2) x;
                   field_at sh t_struct_list [StructField _head] (Vint a) t;
                   field_at sh t_struct_list [StructField _tail] u t;
                   listrep sh s1b u;
                   listrep sh s2 y))%assert.
+ (* current assertion implies loop invariant *)
   Exists v s1' x u.
   subst s1. entailer!. cancel_wand.
+ (* loop test is safe to execute *)
   entailer!.
+ (* loop body preserves invariant *)
  clear v H0.
  rewrite (listrep_nonnull _ _ u0) by auto.
   Intros b s1c z.
   forward. (* t = u; *)
   forward. (* u = t -> tail; *)
   Exists (b,s1c,u0,z). unfold fst, snd.
   simpl app.
   entailer!.
   sep_apply (singleton_lseg sh (b :: s1c ++ s2) a t u0).
   apply wand_frame_ver.
+ (* after the loop *)
   clear v s1' H0.
   forward. (* t -> tail = y; *)
   forward. (* return x; *)
   Exists x.
   rewrite (listrep_null _ s1b) by auto.
   entailer!.
   simpl app.
   sep_apply (singleton_lseg sh s2 a t y).
   unfold lseg; simpl app; apply_wand_frame_elim; cancel.
Qed.

End ProofByWandFrame1.

Module ProofByWandFrame2.

Import LsegWandFrame.
  
Lemma body_append1: semax_body Vprog Gprog f_append1 append1_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  * rewrite (listrep_null _ _ x) by auto. normalize.
    forward. (* return; *)
    Exists y.
    entailer!.
  * forward. (* t = x; *)
    rewrite (listrep_nonnull _ _ x) by auto.
    Intros v s1' u.
    forward. (* u = t -> tail; *)
    forward_while
      ( EX s1a: list int, EX b: int, EX s1c: list int, EX t: val, EX u: val,
            PROP (s1 = s1a ++ b :: s1c)
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (lseg sh (b::s1c++s2) s1a x t;
                 field_at sh t_struct_list [StructField _head] (Vint b) t;
                 field_at sh t_struct_list [StructField _tail] u t;
                 listrep sh s1c u;
                 listrep sh s2 y))%assert.
+ (* current assertion implies loop invariant *)
   Exists (@nil int) v s1' x u.
   subst s1. entailer!. unfold lseg; simpl; cancel_wand.
+ (* loop test is safe to execute *)
   entailer!.
+ (* loop body preserves invariant *)
  clear v H0.
  rewrite (listrep_nonnull _ _ u0) by auto.
  Intros c s1d z.
  forward. (* t = u; *)
   forward. (* u = t -> tail; *)
   Exists ((s1a ++ b :: nil),c,s1d,u0,z). unfold fst, snd.
   simpl app.
   entailer!.
     1: apply (app_assoc s1a [b] (c :: s1d)).
   sep_apply (singleton_lseg sh (c :: s1d ++ s2) b t u0).
   apply lseg_lseg.
+ (* after the loop *)
   clear v s1' H0.
   forward. (* t -> tail = y; *)
   forward. (* return x; *)
   Exists x.
   rewrite (listrep_null _ s1c) by auto.
   entailer!.
   simpl app.
   sep_apply (singleton_lseg sh s2 b t y).
   sep_apply (lseg_lseg sh s1a [b] s2 x t y) using (simpl app).
   sep_apply (list_lseg sh (s1a ++ [b]) s2 x y).
   auto.
Qed.

End ProofByWandFrame2.

Module ProofByWandQFrame.

Import LsegWandQFrame.
  
Lemma body_append1: semax_body Vprog Gprog f_append1 append1_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  * rewrite (listrep_null _ _ x) by auto. normalize.
    forward. (* return; *)
    Exists y.
    entailer!.
  * forward. (* t = x; *)
    rewrite (listrep_nonnull _ _ x) by auto.
    Intros v s1' u.
    forward. (* u = t -> tail; *)
    forward_while
      ( EX s1a: list int, EX b: int, EX s1c: list int, EX t: val, EX u: val,
            PROP (s1 = s1a ++ b :: s1c)
            LOCAL (temp _x x; temp _t t; temp _u u; temp _y y)
            SEP (lseg sh s1a x t;
                 field_at sh t_struct_list [StructField _head] (Vint b) t;
                 field_at sh t_struct_list [StructField _tail] u t;
                 listrep sh s1c u;
                 listrep sh s2 y))%assert.
+ (* current assertion implies loop invariant *)
   Exists (@nil int) v s1' x u.
   subst s1. entailer!. unfold lseg; simpl; apply allp_right; intros; cancel_wand.
+ (* loop test is safe to execute *)
   entailer!.
+ (* loop body preserves invariant *)
  clear v H0.
  rewrite (listrep_nonnull _ _ u0) by auto.
  Intros c s1d z.
  forward. (* t = u; *)
   forward. (* u = t -> tail; *)
   Exists ((s1a ++ b :: nil),c,s1d,u0,z). unfold fst, snd.
   simpl app.
   entailer!.
     1: apply (app_assoc s1a [b] (c :: s1d)).
   sep_apply (singleton_lseg sh (c :: s1d ++ s2) b t u0).
   apply lseg_lseg.
+ (* after the loop *)
   clear v s1' H0.
   forward. (* t -> tail = y; *)
   forward. (* return x; *)
   Exists x.
   rewrite (listrep_null _ s1c) by auto.
   entailer!.
   simpl app.
   sep_apply (singleton_lseg sh s2 b t y).
   sep_apply (lseg_lseg sh s1a [b] x t y) using (simpl app).
   sep_apply (list_lseg sh (s1a ++ [b]) s2 x y).
   auto.
Qed.

End ProofByWandQFrame.

End VerifAppend1.

End VerifAppend.
