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
Require Import progs.malloc_lemmas.
Require Import progs.list_dt.
Require Import progs.test1.

Local Open Scope logic.

Instance LS: listspec t_struct_list _t.
Proof. eapply mk_listspec; reflexivity. Defined.

Definition sum_int := fold_right Int.add Int.zero.

Definition sumlist_spec :=
 DECLARE _sumlist
  WITH sh : share, contents : list int
  PRE [ _p OF (tptr t_struct_list)]  `(lseg LS sh contents) (eval_id _p) `nullval
  POST [ tint ]  local (`(eq (Vint (sum_int contents))) retval).

Definition reverse_spec :=
 DECLARE _reverse
  WITH sh : share, contents : list int
  PRE  [ _p OF (tptr t_struct_list) ] !! writable_share sh &&
              `(lseg LS sh contents) (eval_id _p) `nullval
  POST [ (tptr t_struct_list) ] `(lseg LS sh (rev contents)) retval `nullval.

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog u
  POST [ tint ] main_post prog u.

Definition Vprog : varspecs := (_three, Tarray t_struct_list 3 noattr)::nil.

Definition Gprog : funspecs := 
    sumlist_spec :: reverse_spec :: main_spec::nil.

Definition Gtot := do_builtins (prog_defs prog) ++ Gprog.

Lemma list_cell_eq: forall sh v i,
   list_cell LS sh v i = field_mapsto sh t_struct_list _h v (Vint i).
Proof. intros. simpl_list_cell; auto. Qed.
Hint Rewrite list_cell_eq : normalize.

Lemma lift_list_cell_eq:
  forall sh e v,
   @eq (environ->mpred) (`(list_cell LS sh) e v) 
                  (`(field_mapsto sh t_struct_list _h) e (`Vint v)).
Proof.
  intros. extensionality rho; unfold_lift. simpl_list_cell; auto.
Qed.
Hint Rewrite lift_list_cell_eq : normalize.

Definition sumlist_Inv (sh: share) (contents: list int) : environ->mpred :=
          (EX cts: list int, 
            PROP () LOCAL (`(eq (Vint (Int.sub (sum_int contents) (sum_int cts)))) (eval_id _s)) 
            SEP ( TT ; `(lseg LS sh cts) (eval_id _t) `nullval)).

Lemma body_sumlist: semax_body Vprog Gtot f_sumlist sumlist_spec.
Proof.
start_function.
name t _t.
name p _p.
name s _s.
name h _h.
forward.  (* s = 0; *) 
forward.  (* t = p; *)
forward_while (sumlist_Inv sh contents)
    (PROP() LOCAL (`((fun v => sum_int contents = force_int v) : val->Prop) (eval_id _s)) SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with contents.
go_lower. subst. normalize. cancel.
(* Prove that loop invariant implies typechecking condition *)
go_lower.
(* Prove that invariant && not loop-cond implies postcondition *)
go_lower.  apply typed_false_ptr in H0. subst.  normalize.
(* Prove that loop body preserves invariant *)
focus_SEP 1; apply semax_lseg_nonnull; [ | intros h' r y ?].
    go_lower. normalize.
normalize.
forward.  (* h = t->h; *)
forward.  (*  t = t->t; *)
forward.  (* s = s + h; *)
(* Prove postcondition of loop body implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with r.
go_lower. subst. inv H1.
 rewrite Int.sub_add_r, Int.add_assoc, (Int.add_commut (Int.neg h')),
             Int.add_neg_zero, Int.add_zero.
normalize. cancel. 
(* After the loop *)
forward.  (* return s; *)
go_lower. 
Qed.

Definition reverse_Inv (sh: share) (contents: list int) : environ->mpred :=
          (EX cts1: list int, EX cts2 : list int,
            PROP (contents = rev cts1 ++ cts2) 
            LOCAL ()
            SEP (`(lseg LS sh cts1) (eval_id _w) `nullval;
                   `(lseg LS sh cts2) (eval_id _v) `nullval)).

Lemma body_reverse: semax_body Vprog Gtot f_reverse reverse_spec.
Proof.
start_function.
name p _p.
name v _v.
name w _w.
name t _t.
forward.  (* w = NULL; *)
forward.  (* v = p; *)
forward_while (reverse_Inv sh contents)
         (PROP() LOCAL () SEP( `(lseg LS sh (rev contents)) (eval_id _w) `nullval)).
(* precondition implies loop invariant *)
unfold reverse_Inv.
apply exp_right with nil.
apply exp_right with contents.
go_lower. subst. simpl; normalize.
(* loop invariant implies typechecking of loop condition *)
go_lower.
(* loop invariant (and not loop condition) implies loop postcondition *)
unfold reverse_Inv.
go_lower. apply typed_false_ptr in H2. subst. normalize. 
    rewrite <- app_nil_end, rev_involutive. auto.
(* loop body preserves invariant *)
normalizex. subst contents.
focus_SEP 1; apply semax_lseg_nonnull; [ | intros h r y ?].
go_lower. normalize.
destruct cts2; inv H0.
forward.  (* t = v->t; *)
forward.  (*  v->t = w; *)
forward.  (*  w = v; *)
forward.  (* v = t; *)
unfold reverse_Inv.
apply exp_right with (h::cts1).
apply exp_right with r.
  go_lower.
  subst v0 y t. rewrite app_ass. normalize.
  rewrite (lseg_unroll _ sh (h::cts1)).
  cancel.
  apply orp_right2.
  unfold lseg_cons.
  apply andp_right.
  apply prop_right.
  destruct w; inv H4; simpl; auto. intro Hx; rewrite Hx in *; inv H1.
  apply exp_right with h.
  apply exp_right with cts1.
  apply exp_right with w0.
  normalize. 
  erewrite (field_mapsto_typecheck_val _ _ _ _ _ _struct_list _  noattr); [ | reflexivity].
  type_of_field_tac.
  normalize.
  assert (eval_cast (tptr t_struct_list)(tptr t_struct_list) w0 = w0)
     by (destruct w0 ; inv H0; simpl; auto).
  rewrite H1 in *.
  apply andp_right.
  apply prop_right; auto.
  cancel. (* end et_10 *)
(* after the loop *)
forward.  (* return w; *)
go_lower. normalize.
Qed.

Lemma setup_globals:
  forall u rho,  tc_environ (func_tycontext f_main Vprog Gtot) rho ->
   main_pre prog u rho
   |-- lseg LS Ews (Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)
             (eval_var _three (Tarray t_struct_list 3 noattr) rho)
      nullval.
Proof.
 unfold main_pre.
 intros _ rho; normalize.
 simpl.
 destruct (globvar_eval_var _ _ _three _ H (eq_refl _) (eq_refl _))
  as [b [z [H97 H99]]]. simpl in *.
 rewrite H97.
 unfold globvar2pred. simpl. rewrite H99. simpl.
 clear.
 rewrite sepcon_emp.
repeat match goal with |- _ * (umapsto _ _ _ ?v * _) |-- _ =>
                apply @lseg_unroll_nonempty1 with v; simpl; auto; 
                apply sepcon_derives; 
                  [rewrite list_cell_eq; umapsto_field_mapsto_tac
                  | ];
                apply sepcon_derives; [umapsto_field_mapsto_tac | ]
           end.
 rewrite lseg_unroll. apply orp_right1.
 unfold ptr_eq;simpl; normalize.
Qed.

Lemma body_main:  semax_body Vprog Gtot f_main main_spec.
Proof.
start_function.
name r _r.
name s _s.
forward.  (*  r = reverse(three); *)
instantiate (1:= (Ews, Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)) in (Value of witness).
 go_lower. normalize. eval_cast_simpl.
  eapply derives_trans; [apply setup_globals; auto | ].
 rewrite prop_true_andp by auto.
 cancel.
auto with closed.
forward.  (* s = sumlist(r); *)
instantiate (1:= (Ews, Int.repr 3 :: Int.repr 2 :: Int.repr 1 :: nil)) in (Value of witness).
go_lower. normalize. cancel.
auto with closed.
forward.  (* return s; *)
go_lower. normalize.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gtot (prog_funct prog) Gtot.
Proof.
unfold Gtot, Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext; [ reflexivity | apply semax_external_FF | ]).
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.
