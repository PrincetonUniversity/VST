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
Require progs.test1.  Module P := progs.test1.
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

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Definition sumlist_Inv (sh: share) (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL (lift1 (partial_sum contents cts) (eval_id P._s)) 
            SEP (TT * lift2 (ilseg sh cts) (eval_id P._t) (lift0 nullval))).

Opaque sepcon.
Opaque emp.
Opaque andp.


Ltac replace_in_pre S S' :=
 match goal with |- semax _ ?P _ _ =>
  match P with context C[S] =>
     let P' := context C[S'] in 
      apply semax_pre with P'; [ | ]
  end
 end.

Lemma body_sumlist: semax_body Vprog Gtot P.f_sumlist sumlist_spec.
Proof.
start_function.
destruct sh_contents as [sh contents]. simpl @fst; simpl @snd.
forward.
forward.
forward_while (sumlist_Inv sh contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P._s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv, partial_sum.
apply exp_right with contents.
(* entailment_tests  et_1 *) 
    go_lower; rewrite H0; rewrite H1; rewrite Int.add_zero_l; normalize; rewrite sepcon_comm; apply sepcon_TT.
(* Prove that loop invariant implies typechecking condition *)
(* entailment_tests  et_2 *) 
  intro; apply TT_right.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold sumlist_Inv, partial_sum.
(* entailment_tests  et_3 *) 
normalize; go_lower; intros;  rewrite H,H0; normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1.
autorewrite with normalize.
apply extract_exists_pre; intro cts.
autorewrite with normalize.
replace_in_pre (ilseg sh cts) (ilseg_cons sh cts).
(* entailment_tests  et_4 *) 
normalize; go_lower; rewrite ilseg_nonnull; normalize.
rewrite lift2_ilseg_cons.
normalizex. intros [[h r] y].
normalizex. subst cts.
simpl list_data; simpl list_link.
forward. normalize.
forward.  intro old_t.
forward.
(* Prove postcondition of loop body implies loop invariant *)
intro x; unfold sumlist_Inv, partial_sum.
apply exp_right with r.
(* entailment_tests  et_5 *) 
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
(* After the loop *)
forward.
(* entailment_tests et_6 *)
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

Definition reverse_Inv (sh: share) (contents: list int) : assert :=
          (EX cts1: list int, EX cts2 : list int,
            PROP (contents = rev cts1 ++ cts2) 
            LOCAL ()
            SEP (lift2 (ilseg sh cts1) (eval_id P._w) (lift0 nullval) *
                   lift2 (ilseg sh cts2) (eval_id P._v) (lift0 nullval))).

Lemma body_reverse: semax_body Vprog Gtot P.f_reverse reverse_spec.
Proof.
start_function.
destruct sh_contents as [sh contents]. simpl @fst; simpl @snd.
normalizex. rename H into WS.
forward.
forward.
forward_while (reverse_Inv sh contents)
         (PROP() LOCAL () SEP( lift2 (ilseg sh (rev contents)) (eval_id P._w) (lift0 nullval))).
(* precondition implies loop invariant *)
unfold reverse_Inv.
apply exp_right with nil.
apply exp_right with contents.
(* entailment_tests et_7 *)
go_lower.
varname P._p _p.
varname P._v _v.
varname P._w _w.
findvars.
subst. simpl; normalize.
(* loop invariant implies typechecking of loop condition *)
(* entailment_tests et_8 *)
normalizex.
(* loop invariant (and not loop condition) implies loop postcondition *)
unfold reverse_Inv.
normalize.
(* entailment_tests et_9 *)
go_lower.
varname P._w _w. varname P._v _v.
rewrite H0. normalize. subst.
rewrite <- app_nil_end. rewrite rev_involutive. auto.
(* loop body preserves invariant *)
unfold reverse_Inv at 1.
normalize.
apply extract_exists_pre; intro cts.
normalize.
apply extract_exists_pre; intro cts2.
normalizex. subst contents.
replace_in_pre (ilseg sh cts2) (ilseg_cons sh cts2).
(* entailment_tests et_12 *)
normalize. 
go_lower.
rewrite (ilseg_nonnull sh cts2) by auto.
normalize.
rewrite lift2_ilseg_cons.
normalizex. intros [[h r] y].
normalizex; subst cts2.
simpl list_data; simpl list_link.
forward. normalize.

(* forward *)
  match goal with
  | |- semax ?Delta (PROPx ?P (LOCALx ?Q (SEPx ?R))) 
                     (Ssequence (Sassign (Efield (Ederef ?e _) ?fld ?t2) ?e2) _) _ =>
       apply (semax_pre (PROPx P 
                (LOCALx (tc_expr Delta e :: tc_expr Delta (Ecast e2 t2) ::Q) 
                (SEPx R))));
   [  normalize; go_lower; normalize
   | isolate_field_tac e fld R; hoist_later_in_pre;
      eapply semax_seq; [ apply sequential'; store_field_tac1   |  ]
   ]
  end.
forward. intro old_w.
forward.
intros.
unfold reverse_Inv.
apply exp_right with (h::cts).
apply exp_right with r.
(* entailment_tests et_10 *)


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
(* after the loop *)
forward.
(* entailment_tests et_11 *)
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
 unfold ilseg;  normalize. simpl.
 apply  lseg_unroll_nonempty1 with (Vptr b (Int.add z (Int.repr 8))); simpl; auto.
 apply sepcon_derives; [mapsto_field_mapsto_tac | ].
 apply sepcon_derives; [mapsto_field_mapsto_tac | ].
 apply  lseg_unroll_nonempty1 with (Vptr b (Int.add z (Int.repr 16))); simpl; auto.
 apply sepcon_derives; [mapsto_field_mapsto_tac | ].
 apply sepcon_derives; [mapsto_field_mapsto_tac | ].
 apply  lseg_unroll_nonempty1 with nullval; simpl; auto.
 apply sepcon_derives; [mapsto_field_mapsto_tac | ].
 match goal with |- ?A |-- _ => rewrite <- (sepcon_emp A) end.
 apply sepcon_derives; [mapsto_field_mapsto_tac | ].
  rewrite lseg_unroll. apply orp_right1.
  rewrite prop_true_andp. normalize.
  unfold ptr_eq. simpl. normalize.
Qed.

Lemma body_main:  semax_body Vprog Gtot P.f_main main_spec.
Proof.
start_function.
normalize.
forward.
go_lower. normalize. unfold F,x.
instantiate (2:= (Ews, Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)).
instantiate (1:=nil).
rewrite prop_true_andp by (compute; intuition).
rewrite prop_true_andp by auto.
destruct u; simpl. normalize.
unfold deref_noload. simpl.
eval_cast_simpl.
apply setup_globals; auto.
unfold x,F in *; clear x F.
apply extract_exists_pre; normalize.
forward.
go_lower. normalize.
unfold x,F.
instantiate (2:= (Ews, Int.repr 3 :: Int.repr 2 :: Int.repr 1 :: nil)).
instantiate (1:=nil).
normalize.
rewrite prop_true_andp by (compute; auto).
eval_cast_simpl.
normalize.
apply extract_exists_pre; intro old.
normalize. clear old.
forward.
normalize; go_lower.  normalize.
rewrite <- H1; reflexivity.
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

