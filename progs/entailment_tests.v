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
PROP  ()
LOCAL 
(tc_environ
   (update_tycon
      (update_tycon Delta (Sset P._s (Econst_int (Int.repr 0) tint)))
      (Sset P._t (Etempvar P._p (tptr P.t_struct_list))));
lift2 eq (eval_id P._t) (eval_expr (Etempvar P._p (tptr P.t_struct_list)));
lift2 eq (eval_id P._s) (eval_expr (Econst_int (Int.repr 0) tint));
tc_formals ((P._p, tptr P.t_struct_list) :: nil))
SEP  (lift2 (ilseg sh contents) (eval_id P._p) (lift0 nullval)*
stackframe_of P.f_sumlist)
|-- PROP  ()
    LOCAL 
    (lift1
       (fun v : val =>
        fold_right Int.add Int.zero contents =
        Int.add (force_int v) (fold_right Int.add Int.zero contents))
       (eval_id P._s))
    SEP  (TT * lift2 (ilseg sh contents) (eval_id P._t) (lift0 nullval)).
Proof.  intros.
 go_lower.
 varname P._t _t.
 varname P._p _p.
 varname P._s _s.
 findvars.
 subst.
 rewrite Int.add_zero_l; normalize; rewrite sepcon_comm; apply sepcon_TT.
Qed.

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Lemma et_2: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
EX  cts : list int,
PROP  ()
LOCAL  (lift1 (partial_sum contents cts) (eval_id P._s))
SEP  (TT * lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval))
  |-- local
      (tc_expr
         (update_tycon
            (update_tycon Delta (Sset P._s (Econst_int (Int.repr 0) tint)))
            (Sset P._t (Etempvar P._p (tptr P.t_struct_list))))
         (Etempvar P._t (tptr P.t_struct_list))).
Proof. intros.
 intro; apply TT_right.
Qed.

Lemma et_3: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in

local
  (lift1 (typed_false (typeof (Etempvar P._t (tptr P.t_struct_list))))
     (eval_expr (Etempvar P._t (tptr P.t_struct_list)))) &&
(EX  cts : list int,
 PROP  ()
 LOCAL 
 (lift1
    (fun v : val =>
     fold_right Int.add Int.zero contents =
     Int.add (force_int v) (fold_right Int.add Int.zero cts)) (eval_id P._s))
   SEP  (TT * lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval)))
|-- overridePost
      (PROP  ()
       LOCAL 
       (lift1
          (fun v : val => fold_right Int.add Int.zero contents = force_int v)
          (eval_id P._s))  SEP  (TT))
      (frame_ret_assert
         (function_body_ret_assert tint
            (local
               (lift1 (eq (Vint (fold_right Int.add Int.zero contents)))
                  retval))) (stackframe_of P.f_sumlist)) EK_normal None.
Proof. intros.
normalize. go_lower.
  rewrite H, H0. normalize.
Qed.

Lemma et_4: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
forall (cts : list int),
local
  (tc_environ
     (update_tycon
        (update_tycon Delta (Sset P._s (Econst_int (Int.repr 0) tint)))
        (Sset P._t (Etempvar P._p (tptr P.t_struct_list))))) &&
PROP  ()
LOCAL 
(lift1 (typed_true (typeof (Etempvar P._t (tptr P.t_struct_list))))
   (eval_id P._t); lift1 (partial_sum contents cts) (eval_id P._s))
SEP  (TT * lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval))
|-- PROP  ()
    LOCAL 
    (lift1 (typed_true (typeof (Etempvar P._t (tptr P.t_struct_list))))
       (eval_id P._t); lift1 (partial_sum contents cts) (eval_id P._s))
    SEP  (TT * lift2 (ilseg_cons sh cts) (eval_id P._t) (lift0 nullval)).
Proof. intros.
normalize; go_lower; rewrite ilseg_nonnull; normalize.
Qed.

Lemma et_5: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in
 forall (h: int) (r: list int) (y: val) (old_t: val) (x: val),
PROP  ()
LOCAL 
(tc_environ
   (exit_tycon
      (Sset P._s (Ebinop Oadd (Etempvar P._s tint) (Etempvar P._h tint) tint))
      (initialized P._t
         (initialized P._h (initialized P._t (initialized P._s Delta))))
      EK_normal);
lift2 eq (eval_id P._s)
  (lift2
     (eval_binop Oadd (typeof (Etempvar P._s tint))
        (typeof (Etempvar P._h tint))) (lift0 x) (eval_id P._h));
lift2 eq (eval_id P._t) (lift0 y); lift2 eq (eval_id P._h) (lift0 (Vint h));
lift2 ptr_neq (lift0 old_t) (lift0 nullval);
lift0 (typed_true (typeof (Etempvar P._t (tptr P.t_struct_list))) old_t);
lift0
  (fold_right Int.add Int.zero contents =
   Int.add (force_int x) (fold_right Int.add Int.zero (h :: r))))
SEP  (lift2 (field_mapsto sh P.t_struct_list P._t) (lift0 old_t) (lift0 y)*
lift2 (field_mapsto sh P.t_struct_list P._h) (lift0 old_t) (lift0 (Vint h))*
lift2 (ilseg sh r) (lift0 y) (lift0 nullval)* TT)
|-- PROP  ()
    LOCAL 
    (lift1
       (fun v : val =>
        fold_right Int.add Int.zero contents =
        Int.add (force_int v) (fold_right Int.add Int.zero r)) (eval_id P._s))
      SEP  (TT * lift2 (ilseg sh r) (eval_id P._t) (lift0 nullval)).
Proof. intros.
go_lower.
varname P._s _s.
varname P._t  _t.
varname P._h _h.
findvars.
subst. rewrite H5; clear H5.
destruct (tc_val_extract_int _ _ _ _ H6) as [n H5].
rewrite H5 in *.
simpl.
destruct x; inv H5.
simpl.
rewrite (Int.add_assoc i h). normalize.
rewrite <- (sepcon_comm TT).
repeat rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
normalize.
Qed.

Lemma et_6: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_sumlist Vprog Gtot  in

local
  (tc_environ
     (update_tycon
        (update_tycon
           (update_tycon Delta (Sset P._s (Econst_int (Int.repr 0) tint)))
           (Sset P._t (Etempvar P._p (tptr P.t_struct_list))))
        (Swhile (Etempvar P._t (tptr P.t_struct_list))
           (Ssequence
              (Sset P._h
                 (Efield
                    (Ederef (Etempvar P._t (tptr P.t_struct_list))
                       P.t_struct_list) P._h tint))
              (Ssequence
                 (Sset P._t
                    (Efield
                       (Ederef (Etempvar P._t (tptr P.t_struct_list))
                          P.t_struct_list) P._t (tptr P.t_struct_list)))
                 (Sset P._s
                    (Ebinop Oadd (Etempvar P._s tint) (Etempvar P._h tint)
                       tint))))))) &&
PROP  ()
LOCAL 
(lift1 (fun v : val => fold_right Int.add Int.zero contents = force_int v)
   (eval_id P._s))  SEP  (TT)
|-- tc_expropt
      (update_tycon
         (update_tycon
            (update_tycon Delta (Sset P._s (Econst_int (Int.repr 0) tint)))
            (Sset P._t (Etempvar P._p (tptr P.t_struct_list))))
         (Swhile (Etempvar P._t (tptr P.t_struct_list))
            (Ssequence
               (Sset P._h
                  (Efield
                     (Ederef (Etempvar P._t (tptr P.t_struct_list))
                        P.t_struct_list) P._h tint))
               (Ssequence
                  (Sset P._t
                     (Efield
                        (Ederef (Etempvar P._t (tptr P.t_struct_list))
                           P.t_struct_list) P._t (tptr P.t_struct_list)))
                  (Sset P._s
                     (Ebinop Oadd (Etempvar P._s tint) (Etempvar P._h tint)
                        tint)))))) (Some (Etempvar P._s tint))
      (ret_type
         (update_tycon
            (update_tycon
               (update_tycon Delta (Sset P._s (Econst_int (Int.repr 0) tint)))
               (Sset P._t (Etempvar P._p (tptr P.t_struct_list))))
            (Swhile (Etempvar P._t (tptr P.t_struct_list))
               (Ssequence
                  (Sset P._h
                     (Efield
                        (Ederef (Etempvar P._t (tptr P.t_struct_list))
                           P.t_struct_list) P._h tint))
                  (Ssequence
                     (Sset P._t
                        (Efield
                           (Ederef (Etempvar P._t (tptr P.t_struct_list))
                              P.t_struct_list) P._t (tptr P.t_struct_list)))
                     (Sset P._s
                        (Ebinop Oadd (Etempvar P._s tint)
                           (Etempvar P._h tint) tint))))))) &&
    lift2
      (frame_ret_assert
         (function_body_ret_assert tint
            (local
               (lift1 (eq (Vint (fold_right Int.add Int.zero contents)))
                  retval))) (stackframe_of P.f_sumlist) EK_return)
      (cast_expropt (Some (Etempvar P._s tint))
         (ret_type
            (update_tycon
               (update_tycon
                  (update_tycon Delta
                     (Sset P._s (Econst_int (Int.repr 0) tint)))
                  (Sset P._t (Etempvar P._p (tptr P.t_struct_list))))
               (Swhile (Etempvar P._t (tptr P.t_struct_list))
                  (Ssequence
                     (Sset P._h
                        (Efield
                           (Ederef (Etempvar P._t (tptr P.t_struct_list))
                              P.t_struct_list) P._h tint))
                     (Ssequence
                        (Sset P._t
                           (Efield
                              (Ederef (Etempvar P._t (tptr P.t_struct_list))
                                 P.t_struct_list) P._t (tptr P.t_struct_list)))
                        (Sset P._s
                           (Ebinop Oadd (Etempvar P._s tint)
                              (Etempvar P._h tint) tint)))))))) id.
Proof. intros.
normalize.
go_lower.
varname P._s _s.
findvars.
repeat apply andp_right; normalize.
rewrite H0.
unfold tint; rewrite eval_cast_int by auto.
apply andp_right; apply prop_right.
auto.
destruct _s; inv H1; auto.
Qed.

Lemma et_7: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
 PROP  ()
LOCAL 
(tc_environ
   (update_tycon
      (update_tycon Delta
         (Sset P._w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      (Sset P._v (Etempvar P._p (tptr P.t_struct_list))));
lift2 eq (eval_id P._v) (eval_expr (Etempvar P._p (tptr P.t_struct_list)));
lift2 eq (eval_id P._w)
  (eval_expr (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)));
lift2 and (lift1 (tc_val (tptr P.t_struct_list)) (eval_id P._p)) (lift0 True))

SEP  (lift2 (ilseg sh contents) (eval_id P._p) (lift0 nullval)*
stackframe_of P.f_reverse)
|-- PROP  (contents = rev nil ++ contents)
    LOCAL ()
    SEP 
    (lift2 (ilseg sh nil) (eval_id P._w) (lift0 nullval) *
     lift2 (ilseg sh contents) (eval_id P._v) (lift0 nullval)).
Proof. intros.
go_lower.
varname P._p _p.
varname P._v _v.
varname P._w _w.
findvars.
subst. simpl; normalize.
Qed.

Lemma et_8: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
EX  cts1 : list int,
(EX  cts2 : list int,
 PROP  (contents = rev cts1 ++ cts2)
 LOCAL ()
 SEP 
 (lift2 (ilseg sh cts1) (eval_id P._w) (lift0 nullval) *
  lift2 (ilseg sh cts2) (eval_id P._v) (lift0 nullval)))
|-- local
      (tc_expr
         (update_tycon
            (update_tycon Delta
               (Sset P._w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
            (Sset P._v (Etempvar P._p (tptr P.t_struct_list))))
         (Etempvar P._v (tptr P.t_struct_list))).
Proof.
intros.
normalize.
intros.
go_lower. apply prop_right; repeat split.
Qed.

Lemma et_9: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (cts1 cts2 : list int),
PROP  (contents = rev cts1 ++ cts2)
LOCAL 
(lift1 (typed_false (typeof (Etempvar P._v (tptr P.t_struct_list))))
   (eval_id P._v))
SEP 
(lift2 (ilseg sh cts1) (eval_id P._w) (lift0 nullval) *
 lift2 (ilseg sh cts2) (eval_id P._v) (lift0 nullval))
|-- PROP  ()
    LOCAL ()
    SEP  (lift2 (ilseg sh (rev contents)) (eval_id P._w) (lift0 nullval)).
Proof. intros.
go_lower.
varname P._w _w. varname P._v _v.
rewrite H0. normalize. subst.
rewrite <- app_nil_end. rewrite rev_involutive. auto.
Qed.

Lemma et_12: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (cts cts2 : list int),
local
  (tc_environ
     (update_tycon
        (update_tycon Delta
           (Sset P._w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        (Sset P._v (Etempvar P._p (tptr P.t_struct_list))))) &&
PROP  ()
LOCAL 
(lift1 (typed_true (typeof (Etempvar P._v (tptr P.t_struct_list))))
   (eval_id P._v))
SEP  (lift2 (ilseg sh cts) (eval_id P._w) (lift0 nullval)*
lift2 (ilseg sh cts2) (eval_id P._v) (lift0 nullval))
|-- PROP  ()
    LOCAL 
    (lift1 (typed_true (typeof (Etempvar P._v (tptr P.t_struct_list))))
       (eval_id P._v))
    SEP  (lift2 (ilseg sh cts) (eval_id P._w) (lift0 nullval)*
    lift2 (ilseg_cons sh cts2) (eval_id P._v) (lift0 nullval)).
Proof. intros.
normalize. 
go_lower.
rewrite (ilseg_nonnull sh cts2) by auto.
normalize.
Qed.

Lemma et_10: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in
  forall (cts : list int) (h : int) (r : list int) (y : val) (old_w : val) (x : val),
PROP  ()
LOCAL 
(tc_environ
   (exit_tycon (Sset P._v (Etempvar P._t (tptr P.t_struct_list)))
      (update_tycon
         (update_tycon
            (initialized P._t (initialized P._v (initialized P._w Delta)))
            (Sassign
               (Efield
                  (Ederef (Etempvar P._v (tptr P.t_struct_list))
                     P.t_struct_list) P._t (tptr P.t_struct_list))
               (Etempvar P._w (tptr P.t_struct_list))))
         (Sset P._w (Etempvar P._v (tptr P.t_struct_list)))) EK_normal);
lift2 eq (eval_id P._v) (eval_id P._t); lift2 eq (eval_id P._w) (lift0 x);
lift2 eq (eval_id P._t) (lift0 y); lift2 ptr_neq (lift0 x) (lift0 nullval);
lift0 (typed_true (typeof (Etempvar P._v (tptr P.t_struct_list))) x))
SEP 
(lift2 (field_mapsto sh P.t_struct_list P._t) (lift0 x)
   (lift0
      (eval_cast (typeof (Etempvar P._w (tptr P.t_struct_list)))
         (tptr P.t_struct_list) old_w))*
lift2 (field_mapsto sh list_struct P._h) (lift0 x) (lift0 (Vint h))*
lift2 (ilseg sh r) (lift0 y) (lift0 nullval)*
lift2 (ilseg sh cts) (lift0 old_w) (lift0 nullval))
|-- PROP  (rev cts ++ h :: r = rev (h :: cts) ++ r)
    LOCAL ()
    SEP 
    (lift2 (ilseg sh (h :: cts)) (eval_id P._w) (lift0 nullval) *
     lift2 (ilseg sh r) (eval_id P._v) (lift0 nullval)).
Proof. intros.

go_lower.
varname P._w _w.
varname P._v _v.
varname P._t _t.
findvars.
subst x y _t.
 normalize. rewrite app_ass. normalize.
rewrite (ilseg_unroll sh (h::cts)).
apply derives_trans with (ilseg_cons sh (h :: cts) _w nullval *
    ilseg sh r _v nullval).
unfold ilseg_cons, lseg_cons.
normalize. apply exp_right with (Vint h).
normalize. apply exp_right with (map Vint cts).
normalize. apply exp_right with old_w.
normalize. 
simpl list_data; simpl list_link.
erewrite (field_mapsto_typecheck_val _ _ _ _ _ P._struct_list _  noattr); [ | reflexivity].
type_of_field_tac.
normalize.
assert (eval_cast (tptr P.t_struct_list)(tptr P.t_struct_list) old_w = old_w)
  by (destruct old_w ; inv H; simpl; auto).
rewrite H0 in *.
normalize.
repeat pull_right (field_mapsto sh list_struct P._t _w old_w).
apply sepcon_derives; auto.
repeat pull_right (field_mapsto sh list_struct P._h _w (Vint h)).
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
apply now_later.
apply sepcon_derives; auto.
apply orp_right2; auto.
Qed.


Lemma et_11: forall (sh: share) (contents: list int),
    let Delta := func_tycontext P.f_reverse Vprog Gtot in

local
  (tc_environ
     (update_tycon
        (update_tycon
           (update_tycon Delta
              (Sset P._w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
           (Sset P._v (Etempvar P._p (tptr P.t_struct_list))))
        (Swhile (Etempvar P._v (tptr P.t_struct_list))
           (Ssequence
              (Sset P._t
                 (Efield
                    (Ederef (Etempvar P._v (tptr P.t_struct_list))
                       P.t_struct_list) P._t (tptr P.t_struct_list)))
              (Ssequence
                 (Sassign
                    (Efield
                       (Ederef (Etempvar P._v (tptr P.t_struct_list))
                          P.t_struct_list) P._t (tptr P.t_struct_list))
                    (Etempvar P._w (tptr P.t_struct_list)))
                 (Ssequence
                    (Sset P._w (Etempvar P._v (tptr P.t_struct_list)))
                    (Sset P._v (Etempvar P._t (tptr P.t_struct_list))))))))) &&
PROP  ()
LOCAL ()
SEP  (lift2 (ilseg sh (rev contents)) (eval_id P._w) (lift0 nullval))
|-- tc_expropt
      (update_tycon
         (update_tycon
            (update_tycon Delta
               (Sset P._w (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
            (Sset P._v (Etempvar P._p (tptr P.t_struct_list))))
         (Swhile (Etempvar P._v (tptr P.t_struct_list))
            (Ssequence
               (Sset P._t
                  (Efield
                     (Ederef (Etempvar P._v (tptr P.t_struct_list))
                        P.t_struct_list) P._t (tptr P.t_struct_list)))
               (Ssequence
                  (Sassign
                     (Efield
                        (Ederef (Etempvar P._v (tptr P.t_struct_list))
                           P.t_struct_list) P._t (tptr P.t_struct_list))
                     (Etempvar P._w (tptr P.t_struct_list)))
                  (Ssequence
                     (Sset P._w (Etempvar P._v (tptr P.t_struct_list)))
                     (Sset P._v (Etempvar P._t (tptr P.t_struct_list))))))))
      (Some (Etempvar P._w (tptr P.t_struct_list)))
      (ret_type
         (update_tycon
            (update_tycon
               (update_tycon Delta
                  (Sset P._w
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
               (Sset P._v (Etempvar P._p (tptr P.t_struct_list))))
            (Swhile (Etempvar P._v (tptr P.t_struct_list))
               (Ssequence
                  (Sset P._t
                     (Efield
                        (Ederef (Etempvar P._v (tptr P.t_struct_list))
                           P.t_struct_list) P._t (tptr P.t_struct_list)))
                  (Ssequence
                     (Sassign
                        (Efield
                           (Ederef (Etempvar P._v (tptr P.t_struct_list))
                              P.t_struct_list) P._t (tptr P.t_struct_list))
                        (Etempvar P._w (tptr P.t_struct_list)))
                     (Ssequence
                        (Sset P._w (Etempvar P._v (tptr P.t_struct_list)))
                        (Sset P._v (Etempvar P._t (tptr P.t_struct_list))))))))) &&
    lift2
      (frame_ret_assert
         (function_body_ret_assert (tptr P.t_struct_list)
            (lift2 (ilseg sh (rev contents)) retval (lift0 nullval)))
         (stackframe_of P.f_reverse) EK_return)
      (cast_expropt (Some (Etempvar P._w (tptr P.t_struct_list)))
         (ret_type
            (update_tycon
               (update_tycon
                  (update_tycon Delta
                     (Sset P._w
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
                  (Sset P._v (Etempvar P._p (tptr P.t_struct_list))))
               (Swhile (Etempvar P._v (tptr P.t_struct_list))
                  (Ssequence
                     (Sset P._t
                        (Efield
                           (Ederef (Etempvar P._v (tptr P.t_struct_list))
                              P.t_struct_list) P._t (tptr P.t_struct_list)))
                     (Ssequence
                        (Sassign
                           (Efield
                              (Ederef (Etempvar P._v (tptr P.t_struct_list))
                                 P.t_struct_list) P._t (tptr P.t_struct_list))
                           (Etempvar P._w (tptr P.t_struct_list)))
                        (Ssequence
                           (Sset P._w (Etempvar P._v (tptr P.t_struct_list)))
                           (Sset P._v (Etempvar P._t (tptr P.t_struct_list))))))))))
      id.
Proof. intros.
normalize.
go_lower.
varname P._w _w.
findvars.
normalize.
apply andp_right.
apply prop_right; repeat split.
erewrite eval_cast_pointer2; try eassumption; simpl; reflexivity.
erewrite eval_cast_pointer2; try eassumption; simpl; auto; reflexivity.
Qed.