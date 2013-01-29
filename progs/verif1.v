Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.forward.
Require Import progs.list.
Require progs.test1.  Module P := progs.test1.

Local Open Scope logic.

Instance LS: listspec P._struct_list P._h tint P._t.
Proof.
apply mk_listspec.
intro Hx; inv Hx.
reflexivity.
econstructor; simpl; reflexivity.
Defined.

Definition sum_int := fold_right Int.add Int.zero.

Definition sumlist_spec :=
 DECLARE P._sumlist
  WITH sh : share, contents : list int
  PRE [ P._p OF (tptr P.t_struct_list)]  lift2 (lseg LS sh (map Vint contents)) 
                                       (eval_id P._p) (lift0 nullval)
  POST [ tint ]  local (lift1 (eq (Vint (sum_int contents))) retval).

Definition reverse_spec :=
 DECLARE P._reverse
  WITH sh : share, contents : list int
  PRE  [ P._p OF (tptr P.t_struct_list) ] !! writable_share sh &&
              lift2 (lseg LS sh (map Vint contents)) (eval_id P._p) (lift0 nullval)
  POST [ (tptr P.t_struct_list) ] lift2 (lseg LS sh (rev (map Vint contents))) retval (lift0 nullval).

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

Definition sumlist_Inv (sh: share) (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL (lift1 (eq (Vint (Int.sub (sum_int contents) (sum_int cts)))) (eval_id P._s)) 
            SEP ( TT ; lift2 (lseg LS sh (map Vint cts)) (eval_id P._t) (lift0 nullval))).

Hint Rewrite @lseg_eq using reflexivity: normalize.

Lemma body_sumlist: semax_body Vprog Gtot P.f_sumlist sumlist_spec.
Proof.
start_function.
name _t P._t.
name _p P._p.
name _s P._s.
name _h P._h.
forward.  (* s = 0; *) 
forward.  (* t = p; *)
forward_while (sumlist_Inv sh contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P._s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with contents.
go_lower. subst. cancel.
(* Prove that loop invariant implies typechecking condition *)
go_lower.
(* Prove that invariant && not loop-cond implies postcondition *)
go_lower.  subst.  normalize. destruct cts; inv H. simpl. normalize.
(* Prove that loop body preserves invariant *)
focus_SEP 1; apply semax_lseg_nonnull; [ | intros h r y ?].
go_lower. destruct cts; inv H.
forward.  (* h = t->h; *)
forward.  (*  t = t->t; *)
forward.  (* s = s + h; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with cts.
go_lower. subst. inv H0.
 rewrite Int.sub_add_r, Int.add_assoc, (Int.add_commut (Int.neg i)),
             Int.add_neg_zero, Int.add_zero.
normalize. cancel. 
(* After the loop *)
forward.  (* return s; *)
go_lower. reflexivity.
Qed.

Definition reverse_Inv (sh: share) (contents: list int) : assert :=
          (EX cts1: list int, EX cts2 : list int,
            PROP (contents = rev cts1 ++ cts2) 
            LOCAL ()
            SEP (lift2 (lseg LS sh (map Vint cts1)) (eval_id P._w) (lift0 nullval);
                   lift2 (lseg LS sh (map Vint cts2)) (eval_id P._v) (lift0 nullval))).

Lemma body_reverse: semax_body Vprog Gtot P.f_reverse reverse_spec.
Proof.
start_function.
name _p P._p.
name _v P._v.
name _w P._w.
name _t P._t.
forward.  (* w = NULL; *)
forward.  (* v = p; *)
forward_while (reverse_Inv sh contents)
         (PROP() LOCAL () SEP( lift2 (lseg LS sh (map Vint (rev contents))) (eval_id P._w) (lift0 nullval))).
(* precondition implies loop invariant *)
unfold reverse_Inv.
apply exp_right with nil.
apply exp_right with contents.
go_lower. subst. simpl; normalize.
(* loop invariant implies typechecking of loop condition *)
go_lower.
(* loop invariant (and not loop condition) implies loop postcondition *)
unfold reverse_Inv.
go_lower. subst. normalize. 
    destruct cts2; inv H0. rewrite <- app_nil_end, rev_involutive. auto.
(* loop body preserves invariant *)
normalizex. subst contents.
focus_SEP 1; apply semax_lseg_nonnull; [ | intros h r y ?].
go_lower.
destruct cts2; inv H0.
forward.  (* t = v->t; *)
forward.  (*  v->t = w; *)
forward.  (*  w = v; *)
forward.  (* v = t; *)
unfold reverse_Inv.
apply exp_right with (i::cts1).
apply exp_right with cts2.
  go_lower.
  subst _v0 y _t. rewrite app_ass. normalize.
  rewrite (lseg_unroll _ sh (Vint i:: map Vint cts1)).
  cancel.
  apply orp_right2.
  unfold lseg_cons.
  apply andp_right.
  apply prop_right.
  destruct _w; inv H4; simpl; auto. intro Hx; rewrite Hx in *; inv H1.
  apply exp_right with (Vint i).
  apply exp_right with (map Vint cts1).
  apply exp_right with _w0.
  normalize. 
  erewrite (field_mapsto_typecheck_val _ _ _ _ _ P._struct_list _  noattr); [ | reflexivity].
  type_of_field_tac.
  normalize.
  assert (eval_cast (tptr P.t_struct_list)(tptr P.t_struct_list) _w0 = _w0)
     by (destruct _w0 ; inv H0; simpl; auto).
  rewrite H1 in *.
  apply andp_right.
  apply prop_right; auto.
  cancel. (* end et_10 *)
(* after the loop *)
forward.  (* return w; *)
go_lower. rewrite map_rev. cancel.
Qed.

Lemma setup_globals:
  forall u rho,  tc_environ (func_tycontext P.f_main Vprog Gtot) rho ->
   main_pre P.prog u rho
   |-- lseg LS Ews (map Vint (Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil))
             (eval_var P._three (Tarray P.t_struct_list 3 noattr) rho)
      nullval.
Proof.
 unfold main_pre.
 intros _ rho; normalize.
 simpl.
 destruct (globvar_eval_var _ _ P._three _ H (eq_refl _) (eq_refl _))
  as [b [z [H97 H99]]]. simpl in *.
 rewrite H97.
 unfold globvar2pred. simpl. rewrite H99. simpl.
 clear.
 rewrite sepcon_emp.
 repeat  match goal with |- _ * (mapsto _ _ _ ?v * _) |-- _ =>
                apply lseg_unroll_nonempty1 with v; simpl; auto; 
                apply sepcon_derives; [mapsto_field_mapsto_tac | ];
                apply sepcon_derives; [mapsto_field_mapsto_tac | ] 
           end.
 rewrite lseg_unroll. apply orp_right1.
 unfold ptr_eq;simpl; normalize.
Qed.

Lemma body_main:  semax_body Vprog Gtot P.f_main main_spec.
Proof.
start_function.
name _r P._r.
name _s P._s.
forward.  (*  r = reverse(three); *)
instantiate (1:= (Ews, Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)) in (Value of x).
go_lower.
eapply derives_trans; [apply setup_globals; auto | ].
cancel.
forward.  (* s = sumlist(r); *)
instantiate (1:= (Ews, Int.repr 3 :: Int.repr 2 :: Int.repr 1 :: nil)) in (Value of x).
go_lower.
forward.  (* return s; *)
go_lower.
normalize.
reflexivity.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct P.prog) Gtot.
Proof.
unfold Gtot, Gprog, P.prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.


