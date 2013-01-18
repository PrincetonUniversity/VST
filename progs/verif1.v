Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.forward.
Require Import progs.list.
Require Import Clightdefs.
Require Import progs.ilseg.
Require progs.test1.  Module P := progs.test1.

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

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Definition sumlist_Inv (sh: share) (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL (lift1 (partial_sum contents cts) (eval_id P._s)) 
            SEP ( TT ; lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval))).


Lemma body_sumlist: semax_body Vprog Gtot P.f_sumlist sumlist_spec.
Proof.
start_function.
name _t P._t.
name _p P._p.
name _s P._s.
name _h P._h.
destruct sh_contents as [sh contents]. simpl @fst; simpl @snd.
forward.  (* s = 0; *)
forward.  (* t = p; *)
forward_while (sumlist_Inv sh contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P._s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv, partial_sum.
apply exp_right with contents.
(* et_1 *)  go_lower. subst; normalize. cancel.
(* Prove that loop invariant implies typechecking condition *)
(* et_2 *)  go_lower.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold partial_sum.
(* et_3 *) go_lower. subst; rewrite H1; normalize.
(* Prove that loop body preserves invariant *)
focus_SEP 1; apply semax_ilseg_nonnull; [ | intros h r y ?; subst cts].
(* et_4 *) go_lower. 
forward.  (* h = t->h; *)
forward.  (*  t = t->t; *)
forward.  (* s = s + h; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold sumlist_Inv, partial_sum.
apply exp_right with r.
(* et_5 *) go_lower. subst. rewrite H4; clear H4 contents.
               destruct _s0; inv H0. normalize.
               rewrite (Int.add_assoc i h). normalize. cancel.
(* After the loop *)
forward.  (* return s; *)
(* et_6 *) go_lower. rewrite H0; reflexivity.
Qed.

Definition reverse_Inv (sh: share) (contents: list int) : assert :=
          (EX cts1: list int, EX cts2 : list int,
            PROP (contents = rev cts1 ++ cts2) 
            LOCAL ()
            SEP (lift2 (ilseg sh cts1) (eval_id P._w) (lift0 nullval);
                   lift2 (ilseg sh cts2) (eval_id P._v) (lift0 nullval))).

Lemma body_reverse: semax_body Vprog Gtot P.f_reverse reverse_spec.
Proof.
start_function.
name _p P._p.
name _v P._v.
name _w P._w.
name _t P._t.
destruct sh_contents as [sh contents].
normalizex. rename H into WS.
forward.  (* w = NULL; *)
forward.  (* v = p; *)
forward_while (reverse_Inv sh contents)
         (PROP() LOCAL () SEP( lift2 (ilseg sh (rev contents)) (eval_id P._w) (lift0 nullval))).
(* precondition implies loop invariant *)
unfold reverse_Inv.
apply exp_right with nil.
apply exp_right with contents.
(* et_7 *) go_lower. subst. simpl; normalize.
(* loop invariant implies typechecking of loop condition *)
(* et_8 *) intro; apply prop_right; repeat split.
(* loop invariant (and not loop condition) implies loop postcondition *)
unfold reverse_Inv.
(*  et_9 *) go_lower. subst _v. normalize. subst. rewrite <- app_nil_end, rev_involutive. auto.
(* loop body preserves invariant *)
normalizex. subst contents.
focus_SEP 1; apply semax_ilseg_nonnull; [ | intros h r y ?; subst cts2].
go_lower.
forward.  (* t = v->t; *)
forward.  (*  v->t = w; *)
forward.  (*  w = v; *)
forward.  (* v = t; *)
unfold reverse_Inv.
apply exp_right with (h::cts1).
apply exp_right with r.
(* et_10 *)
  go_lower.
  subst _v0 y _t. rewrite app_ass. normalize.
  rewrite (ilseg_unroll sh (h::cts1)).
  cancel.
  apply orp_right2.
  unfold ilseg_cons, lseg_cons.
  apply andp_right.
  apply prop_right.
  destruct _w; inv H3; simpl; auto. intro Hx; rewrite Hx in *; inv H1.
  apply exp_right with (Vint h).
  apply exp_right with (map Vint cts1).
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
  cancel. (* end et_10 *)
(* after the loop *)
forward.  (* return w; *)
(* et_11 *) go_lower. eval_cast_simpl. normalize.
Qed.

Lemma setup_globals:
  forall rho,  tc_environ (func_tycontext P.f_main Vprog Gtot) rho ->
   main_pre P.prog tt rho
   |-- ilseg Ews (Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)
             (eval_var P._three (Tarray P.t_struct_list 3 noattr) rho)
      nullval.
Proof.
 unfold main_pre.
 intro rho; normalize.
 simpl.
 destruct (globvar_eval_var _ _ P._three _ H (eq_refl _) (eq_refl _))
  as [b [z [H97 H99]]]. simpl in *.
 rewrite H97.
 unfold globvar2pred. simpl. rewrite H99. simpl.
 clear.
 unfold ilseg; simpl.
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
destruct u.
eval_cast_simpl.
eapply derives_trans; [apply setup_globals; auto | ].
cancel.
forward.  (* s = sumlist(r); *)
instantiate (1:= (Ews, Int.repr 3 :: Int.repr 2 :: Int.repr 1 :: nil)) in (Value of x).
go_lower.
eval_cast_simpl.
cancel.
forward.  (* return s; *)
go_lower.
normalize.
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


