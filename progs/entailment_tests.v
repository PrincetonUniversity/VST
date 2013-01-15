Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.list.
Require Import Clightdefs. 
Require Import progs.test1. Module P := progs.test1.
Require Import progs.ilseg.

Local Open Scope logic.

Definition sumlist_spec :=
 DECLARE P._sumlist
  WITH sh_contents 
  PRE [ P._p : t_listptr]  lift2 (ilseg (fst sh_contents) (snd sh_contents)) (eval_id P._p) (lift0 nullval)
  POST [ tint ]  local (lift1 (eq (Vint (fold_right Int.add Int.zero (snd sh_contents)))) retval).

Definition reverse_spec :=
 DECLARE P._reverse
  WITH sh_contents : share * list int
  PRE  [ P._p : t_listptr ] !! writable_share (fst sh_contents) &&
        lift2 (ilseg (fst sh_contents) (snd sh_contents)) (eval_id P._p) (lift0 nullval)
  POST [ t_listptr ] lift2 (ilseg (fst sh_contents) (rev (snd sh_contents))) retval (lift0 nullval).

Definition main_spec :=
 DECLARE P._main
  WITH u : unit
  PRE  [] main_pre P.prog u
  POST [ tint ] main_post P.prog u.

Definition main_spec' := (P._main, mk_funspec (nil, tint) _ (main_pre P.prog) (main_post P.prog)).

Definition Vprog : varspecs := (P._three, Tarray P.t_struct_list 3 noattr)::nil.

Definition Gprog : funspecs := 
    sumlist_spec :: reverse_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs P.prog) ++ Gprog.

Lemma et_1:
 forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
  forall (_t : name P._t) (_p : name P._p) (_s : name P._s) (_h : name P._h),
PROP  ()
LOCAL 
(tc_environ (initialized P._t (initialized P._s Delta));
lift2 eq (eval_id P._t) (eval_expr (Etempvar P._p (tptr P.t_struct_list)));
lift2 eq (eval_id P._s) (eval_expr (Econst_int (Int.repr 0) tint)))
SEP  (lift2 (ilseg sh contents) (eval_id P._p) (lift0 nullval))
|-- PROP  ()
    LOCAL 
    (lift1
       (fun v : val =>
        fold_right Int.add Int.zero contents =
        Int.add (force_int v) (fold_right Int.add Int.zero contents))
       (eval_id P._s))
    SEP  (TT; lift2 (ilseg sh contents) (eval_id P._t) (lift0 nullval)).
Proof.  intros.
 go_lower. subst; normalize. cancel. 
Qed.

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Lemma et_2: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
  forall (_t : name P._t) (_p : name P._p) (_s : name P._s) (_h : name P._h),
   forall (cts : list int),
PROP  ()
LOCAL  (tc_environ (initialized P._t (initialized P._s Delta));
lift1 (partial_sum contents cts) (eval_id P._s))
SEP  (TT; lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval))
|-- local
      (tc_expr (initialized P._t (initialized P._s Delta))
         (Etempvar P._t (tptr P.t_struct_list))).
Proof. intros.
 go_lower; cancel.
Qed.

Lemma et_3: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
  forall (_t : name P._t) (_p : name P._p) (_s : name P._s) (_h : name P._h),
 forall cts : list int,
PROP  ()
LOCAL  (tc_environ (initialized P._t (initialized P._s Delta));
lift1 (typed_false (typeof (Etempvar P._t (tptr P.t_struct_list))))
  (eval_expr (Etempvar P._t (tptr P.t_struct_list)));
lift1
  (fun v : val =>
   fold_right Int.add Int.zero contents =
   Int.add (force_int v) (fold_right Int.add Int.zero cts)) (eval_id P._s))
SEP  (TT; lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval))
|-- overridePost
      (PROP  ()
       LOCAL 
       (lift1
          (fun v : val => fold_right Int.add Int.zero contents = force_int v)
          (eval_id P._s))  SEP  (TT))
      (function_body_ret_assert tint
         (local
            (lift1 (eq (Vint (fold_right Int.add Int.zero contents))) retval)))
      EK_normal None.
Proof. intros.
 go_lower. subst; rewrite H1. normalize.
Qed.

Lemma et_4: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
  forall (_t : name P._t) (_p : name P._p) (_s : name P._s) (_h : name P._h),
  forall (cts : list int),
PROP  ()
LOCAL  (tc_environ (initialized P._t (initialized P._s Delta));
lift1 (typed_true (typeof (Etempvar P._t (tptr P.t_struct_list))))
  (eval_id P._t); lift1 (partial_sum contents cts) (eval_id P._s))
SEP  (lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval); TT)
|-- local (lift1 (typed_true (tptr P.t_struct_list)) (eval_id P._t)).
Proof. intros.
 go_lower.
Qed.

Lemma et_5: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
  forall (_t : name P._t) (_p : name P._p) (_s : name P._s) (_h : name P._h),
 forall (h: int) (r: list int) (y: val) (old_t: val) (x: val),
PROP  ()
LOCAL 
(tc_environ
   (initialized P._s
      (initialized P._t
         (initialized P._h (initialized P._t (initialized P._s Delta)))));
lift2 eq (eval_id P._s)
  (lift2
     (eval_binop Oadd (typeof (Etempvar P._s tint))
        (typeof (Etempvar P._h tint))) (lift0 x) (eval_id P._h));
lift2 eq (eval_id P._t) (lift0 y); lift2 eq (eval_id P._h) (lift0 (Vint h));
lift0 (typed_true (typeof (Etempvar P._t (tptr P.t_struct_list))) old_t);
lift0
  (fold_right Int.add Int.zero contents =
   Int.add (force_int x) (fold_right Int.add Int.zero (h :: r))))
SEP  (lift2 (field_mapsto sh P.t_struct_list P._t) (lift0 old_t) (lift0 y);
lift2 (field_mapsto sh P.t_struct_list P._h) (lift0 old_t) (lift0 (Vint h));
lift2 (ilseg sh r) (lift0 y) (lift0 nullval); TT)
|-- PROP  ()
    LOCAL 
    (lift1
       (fun v : val =>
        fold_right Int.add Int.zero contents =
        Int.add (force_int v) (fold_right Int.add Int.zero r)) (eval_id P._s))
      SEP  (TT; lift2 (ilseg sh r) (eval_id P._t) (lift0 nullval)).
Proof. intros.
go_lower.
subst. rewrite H4; clear H4 contents.
destruct x; inv H0.
normalize.
rewrite (Int.add_assoc i h). normalize.
cancel.
Qed.

Lemma et_6: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
  forall (_t : name P._t) (_p : name P._p) (_s : name P._s) (_h : name P._h),
PROP  ()
LOCAL  (tc_environ (initialized P._t (initialized P._s Delta));
lift1 (fun v : val => fold_right Int.add Int.zero contents = force_int v)
  (eval_id P._s))  SEP  (TT)
|-- local
      (tc_expropt (initialized P._t (initialized P._s Delta))
         (Some (Etempvar P._s tint))
         (ret_type (initialized P._t (initialized P._s Delta)))) &&
    lift2
      (function_body_ret_assert tint
         (local
            (lift1 (eq (Vint (fold_right Int.add Int.zero contents))) retval))
         EK_return)
      (cast_expropt (Some (Etempvar P._s tint))
         (ret_type (initialized P._t (initialized P._s Delta)))) id.
Proof. intros.
go_lower. apply prop_right; rewrite H0; reflexivity.
Qed.

Lemma et_7: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (_p : name P._p) (_v : name P._v) (_w : name P._w) (_t : name P._t),
  forall (WS: writable_share sh),
PROP  ()
LOCAL  (tc_environ (initialized P._v (initialized P._w Delta));
lift2 eq (eval_id P._v) (eval_expr (Etempvar P._p (tptr P.t_struct_list)));
lift2 eq (eval_id P._w)
  (eval_expr (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
SEP  (lift2 (ilseg sh contents) (eval_id P._p) (lift0 nullval); emp)
|-- PROP  (contents = rev nil ++ contents)
    LOCAL ()
    SEP  (lift2 (ilseg sh nil) (eval_id P._w) (lift0 nullval);
    lift2 (ilseg sh contents) (eval_id P._v) (lift0 nullval)).
Proof. intros.
go_lower. subst. simpl; normalize.
Qed.

Lemma et_8: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (_p : name P._p) (_v : name P._v) (_w : name P._w) (_t : name P._t),
  forall (WS: writable_share sh) (cts1 cts2 : list int),
PROP  (contents = rev cts1 ++ cts2)
LOCAL  (tc_environ (initialized P._v (initialized P._w Delta)))
SEP  (lift2 (ilseg sh cts1) (eval_id P._w) (lift0 nullval);
lift2 (ilseg sh cts2) (eval_id P._v) (lift0 nullval))
|-- local
      (tc_expr (initialized P._v (initialized P._w Delta))
         (Etempvar P._v (tptr P.t_struct_list))).
Proof. intros.
go_lower.
Qed.

Lemma et_9: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (_p : name P._p) (_v : name P._v) (_w : name P._w) (_t : name P._t),
  forall (WS: writable_share sh)  (cts1 cts2 : list int),
PROP  (contents = rev cts1 ++ cts2)
LOCAL  (tc_environ (initialized P._v (initialized P._w Delta));
lift1 (typed_false (typeof (Etempvar P._v (tptr P.t_struct_list))))
  (eval_expr (Etempvar P._v (tptr P.t_struct_list))))
SEP  (lift2 (ilseg sh cts1) (eval_id P._w) (lift0 nullval);
lift2 (ilseg sh cts2) (eval_id P._v) (lift0 nullval))
|-- overridePost
      (PROP  ()
       LOCAL ()
       SEP  (lift2 (ilseg sh (rev contents)) (eval_id P._w) (lift0 nullval)))
      (function_body_ret_assert (tptr P.t_struct_list)
         (lift2 (ilseg sh (rev contents)) retval (lift0 nullval))) EK_normal
      None.
Proof. intros.
go_lower.
subst _v. normalize. subst.
rewrite <- app_nil_end, rev_involutive. auto.
Qed.

Lemma et_10: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (_p : name P._p) (_v : name P._v) (_w : name P._w) (_t : name P._t),
  forall (WS: writable_share sh),
  forall (cts : list int) (h : int) (r : list int) (y : val) (_w0 : val) (_v0 : val),
PROP  ()
LOCAL 
(tc_environ
   (initialized P._v
      (initialized P._w
         (initialized P._t (initialized P._v (initialized P._w Delta)))));
lift2 eq (eval_id P._v) (eval_id P._t);
lift2 eq (eval_id P._w) (lift0 _v0); lift2 eq (eval_id P._t) (lift0 y);
lift0 (typed_true (typeof (Etempvar P._v (tptr P.t_struct_list))) _v0))
SEP 
(lift2 (field_mapsto sh P.t_struct_list P._t) (lift0 _v0)
   (lift0
      (eval_cast (typeof (Etempvar P._w (tptr P.t_struct_list)))
         (tptr P.t_struct_list) _w0));
lift2 (field_mapsto sh list_struct P._h) (lift0 _v0) (lift0 (Vint h));
lift2 (ilseg sh r) (lift0 y) (lift0 nullval);
lift2 (ilseg sh cts) (lift0 _w0) (lift0 nullval))
|-- PROP  (rev cts ++ h :: r = rev (h :: cts) ++ r)
    LOCAL ()
    SEP  (lift2 (ilseg sh (h :: cts)) (eval_id P._w) (lift0 nullval);
    lift2 (ilseg sh r) (eval_id P._v) (lift0 nullval)).
Proof. intros.
go_lower.
subst _v0 y _t. rewrite app_ass. normalize.
cancel.
rewrite (ilseg_unroll sh (h::cts)).
apply orp_right2.
unfold ilseg_cons, lseg_cons.
apply andp_right.
apply prop_right.
clear - H3.
destruct _w; inv H3; simpl; auto. intro Hx; rewrite Hx in *; inv H0.
apply exp_right with (Vint h).
apply exp_right with (map Vint cts).
apply exp_right with _w0.
normalize. 
simpl list_data; simpl list_link.
erewrite (field_mapsto_typecheck_val _ _ _ _ _ P._struct_list _  noattr); [ | reflexivity].
type_of_field_tac.
normalize.
assert (eval_cast (tptr P.t_struct_list)(tptr P.t_struct_list) _w0 = _w0)
  by (destruct _w0 ; inv H0; simpl; auto).
rewrite H1 in *.
apply andp_right.
apply prop_right; auto.
cancel.
Qed.

Lemma et_11: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (_p : name P._p) (_v : name P._v) (_w : name P._w) (_t : name P._t),
  forall (WS: writable_share sh),
PROP  ()
LOCAL  (tc_environ (initialized P._v (initialized P._w Delta)))
SEP  (lift2 (ilseg sh (rev contents)) (eval_id P._w) (lift0 nullval))
|-- local
      (tc_expropt (initialized P._v (initialized P._w Delta))
         (Some (Etempvar P._w (tptr P.t_struct_list)))
         (ret_type (initialized P._v (initialized P._w Delta)))) &&
    lift2
      (function_body_ret_assert (tptr P.t_struct_list)
         (lift2 (ilseg sh (rev contents)) retval (lift0 nullval)) EK_return)
      (cast_expropt (Some (Etempvar P._w (tptr P.t_struct_list)))
         (ret_type (initialized P._v (initialized P._w Delta)))) id.
Proof. intros.
go_lower.
apply andp_right.
apply prop_right; repeat split.
eval_cast_simpl; auto.
eval_cast_simpl; auto.
Qed.