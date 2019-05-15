Require Import VST.floyd.proofauto.
Require Import WandDemo.wand_frame.
Require Import WandDemo.wand_frame_tactic.
Require Import WandDemo.wandQ_frame.
Require Import WandDemo.list.
Require Import WandDemo.list_lemmas.

Lemma Tsh_split: forall sh, exists sh', sepalg.join sh sh' Tsh.
Proof.
  intros.
  exists (Share.comp sh).
  split.
  + apply Share.comp2.
  + apply Share.comp1.
Qed.

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
  WITH sh : share, x: val, y: val, s1: list int, s2: list int
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

Module ProofByNoWandBad.

Import LsegRecursiveLoopFree.

Lemma body_append1: semax_body Vprog Gprog f_append1 append1_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  * rewrite (listrep_null _ _ x) by auto. normalize.
    forward. (* return; *)
    Exists y.
    entailer!.
    simpl app; auto.
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

End ProofByNoWandBad.

Module ProofByNoWandGood.

Import LsegRecursiveMaybeLoop.

Lemma body_append1: semax_body Vprog Gprog f_append1 append1_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  * rewrite (listrep_null _ _ x) by auto. normalize.
    forward. (* return; *)
    Exists y.
    entailer!.
    simpl app; auto.
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
   subst s1. entailer!. unfold lseg; entailer!.
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
   sep_apply (singleton_lseg sh b t u0).
   apply lseg_lseg.
+ (* after the loop *)
   clear v s1' H0.
   forward. (* t -> tail = y; *)
   forward. (* return x; *)
   Exists x.
   rewrite (listrep_null _ s1c) by auto.
   entailer!.
   simpl app.
   sep_apply (singleton_lseg sh b t y).
   sep_apply (lseg_lseg sh s1a [b] x t y).
   sep_apply (list_lseg sh (s1a ++ [b]) s2 x y).
   auto.
Qed.

End ProofByNoWandGood.

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
    simpl app; auto.
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
   subst s1. entailer!. simpl app; cancel_wand.
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
    simpl app; auto.
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
   change (b :: s2) with ([b] ++ s2).
   sep_apply (lseg_lseg sh s1a [b] s2 x t y).
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
    simpl app; auto.
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
   sep_apply (singleton_lseg sh b t u0).
   apply lseg_lseg.
+ (* after the loop *)
   clear v s1' H0.
   forward. (* t -> tail = y; *)
   forward. (* return x; *)
   Exists x.
   rewrite (listrep_null _ s1c) by auto.
   entailer!.
   simpl app.
   sep_apply (singleton_lseg sh b t y).
   sep_apply (lseg_lseg sh s1a [b] x t y).
   sep_apply (list_lseg sh (s1a ++ [b]) s2 x y).
   auto.
Qed.

End ProofByWandQFrame.

End VerifAppend1.

Module VerifAppend2.

Import ListLib.
Import LBsegWandQFrame.

Definition append2_spec := append_spec _append2.

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append2_spec ]).

Lemma data_at__Tsh_wand_frame_intro: forall {CS: compspecs} sh t p,
  writable_share sh ->
  data_at_ Tsh t p |-- data_at_ sh t p *
    ALL v: reptype t, data_at sh t v p -* data_at Tsh t v p.
Proof.
  intros.
  destruct (Tsh_split sh) as [sh' ?].
  unfold data_at_ at 1, field_at_.
  simpl nested_field_type.
  fold (data_at Tsh t (default_val t) p).
  rewrite <- (data_at_share_join  _ _ _ t _ p H0).
  cancel.
  apply allp_right; intros v.
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply (data_at_share_join_W _ _ Tsh t _ _ p); auto.
Qed.

Lemma body_append2: semax_body Vprog Gprog f_append2 append2_spec.
Proof.
  start_function.
  rename v_head into retp.
  rename x into head.
  replace_SEP 0
    (data_at_ sh (tptr t_struct_list) retp * ALL v: val, data_at sh (tptr t_struct_list) v retp -* data_at Tsh (tptr t_struct_list) v retp).
    {
      entailer!.
      apply data_at__Tsh_wand_frame_intro; auto.
    }
  Intros. freeze [1] Fr.
  forward. (* head = x; *)
  forward. (* curp = & head *)
  forward. (* cur = x *)
  forward. (* retp = & head *)
  forward_while
      ( EX s1a: list int, EX s1b: list int, EX curp: val, EX cur: val,
            PROP (s1 = s1a ++ s1b)
            LOCAL (temp _retp retp; temp _cur cur; temp _y y; temp _curp curp; lvar _head (tptr t_struct_list) retp)
            SEP (lbseg sh s1a retp curp;
                 listrep sh s1b cur;
                 listrep sh s2 y;
                 data_at sh (tptr t_struct_list) cur curp;
                 FRZL Fr))%assert.
  + (* current assertion implies loop invariant *)
    Exists (@nil int) s1 retp head.
    entailer!. unfold lbseg; simpl; apply allp_right; intros; cancel_wand.
  + (* loop test is safe to execute *)
    entailer!.
  + (* loop body preserves invariant *)
    forward. (* curp = & (cur -> tail); *)
    assert_PROP (offset_val
              (align (align 0 (alignof tint) + sizeof tint)
                (alignof (tptr (Tstruct _list noattr)))) cur =
                 field_address t_struct_list [StructField _tail] cur).
    {
      entailer!.
      symmetry; apply field_address_eq_offset'; auto.
      auto with field_compatible.
    }
    rewrite H0; clear H0.
    rewrite (listrep_nonnull _ _ cur) by auto.
    Intros b s1c next.
    subst s1b.
    forward. (* cur = * curp *)
    Exists (s1a ++ [b], s1c, (field_address t_struct_list [StructField _tail] cur), next).
    simpl snd; simpl fst.
    entailer!.
      1: rewrite <- app_assoc; auto.
    sep_apply (singleton_lbseg sh b curp cur).
    sep_apply (lbseg_lbseg sh s1a [b] retp curp (field_address t_struct_list [StructField _tail] cur)).
    auto.
  + (* After loop *)
    rewrite (listrep_null _ _ cur) by auto.
    Intros.
    forward. (* * curp = y *)
    gather_SEP emp (listrep _ _ _) (data_at _ _ _ _).
    replace_SEP 0 (listboxrep sh s2 curp).
    {
      entailer!.
      unfold listboxrep; Exists y.
      cancel.
    }
    gather_SEP (listboxrep _ _ _) (lbseg _ _ _ _).
    replace_SEP 0 (listboxrep sh (s1a ++ s2) retp).
    {
      entailer!.
      (** This step can also be done by
            [wandQ_frame_tactic.solve_wandQ lbseg]. *)
      sep_apply (listbox_lbseg sh s1a s2 retp curp).
      cancel.
    }
    unfold listboxrep; Intros head'.
    thaw Fr.
    gather_SEP (data_at _ _ _ _) (allp _).
    replace_SEP 0 (data_at Tsh (tptr t_struct_list) head' retp).
    {
      entailer!.
      rewrite sepcon_comm; apply wand_sepcon_adjoint.
      apply (allp_left _ head').
      auto.
    }
    forward. (* ret = * retp *)
    forward. (* return ret *)
    Exists head'.
    entailer!.
    rewrite app_nil_r.
    auto.
Qed.

End VerifAppend2.

Module VerifAppend3.

Import ListLib.
Import LsegWandQFrame.

Definition append3_spec := append_spec _append3.

Definition Gprog : funspecs :=
  ltac:(with_library prog [ append3_spec ]).

Lemma body_append3: semax_body Vprog Gprog f_append3 append3_spec.
Proof.
  start_function.
  forward_if. (* if (x == NULL) *)
  + forward. (* return y; *)
    rewrite (listrep_null _ _ nullval) by auto.
    Exists y; entailer!. simpl app; auto.
  + rewrite (listrep_nonnull _ _ x) by auto.
    Intros a s1b x'.
    subst s1.
    forward. (* t = x -> tail; *)
    forward_call (sh, x', y, s1b, s2). (* t = append3(t, y); *)
    Intros x''.
    forward. (* x -> tail = t; *)
    forward. (* return x *)
    Exists x.
    entailer!.
    simpl app.
    unfold listrep at 2; fold listrep.
    Exists x''.
    entailer!.
Qed.

End VerifAppend3.

End VerifAppend.
