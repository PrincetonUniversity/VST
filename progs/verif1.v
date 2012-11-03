Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import compcert.Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.forward.
Require Import progs.list.

Local Open Scope logic.

Require progs.test1.
Module P := progs.test1.

Local Open Scope logic.

Instance t_list_spec: listspec P.t_listptr.
Proof.
econstructor.
reflexivity.
intro Hx; inv Hx.
intros.
unfold unroll_composite; simpl.
reflexivity.
econstructor; simpl; reflexivity.
Defined.

Definition ilseg (s: list int) := lseg P.t_listptr (map Vint s).

Definition ilseg_nil (l: list  int) x z : mpred := !! (ptr_eq x z) && !! (l=nil) && emp.
Definition ilseg_cons (s: list int) := lseg_cons P.t_listptr (map Vint s).

Lemma ilseg_unroll: forall l x z , 
    ilseg l x z = ilseg_nil l x z || ilseg_cons l x z.
Proof.
intros.
unfold ilseg at 1.
rewrite lseg_unroll.
unfold ilseg_cons, ilseg_nil, ilseg.
f_equal.
f_equal. f_equal.
f_equal.
apply prop_ext; split; intro; destruct l; simpl in *; congruence.
Qed.

Lemma ilseg_eq: forall s p, 
   typecheck_val p P.t_listptr = true -> 
    (ilseg s p p = !!(s=nil) && emp).
Proof. intros. unfold ilseg. rewrite lseg_eq; auto. f_equal. f_equal.
 apply prop_ext. destruct s; simpl; intuition congruence.
Qed.
Hint Rewrite ilseg_eq : normalize.

Lemma ilseg_nonnull:
  forall s v,
      typed_true P.t_listptr v ->
     ilseg s v nullval = ilseg_cons s v nullval.
Proof.
intros. subst. 
rewrite ilseg_unroll.
unfold ilseg_cons, ilseg_nil.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
rewrite H0 in H. inv H.
intros.
normalize.
apply orp_right2.
assert (~ ptr_eq v nullval).
intro. unfold typed_true,ptr_eq in *. destruct v; simpl in *; auto.
rewrite H0 in H; inv H.
normalize.
Qed.

Lemma ilseg_nil_eq: forall p q, ilseg nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite ilseg_unroll.
 apply pred_ext.
 apply orp_left.
 unfold ilseg_nil.  normalize.
 unfold ilseg_cons. normalize. unfold lseg_cons. normalize. intros. inv H0.
 apply orp_right1. unfold ilseg_nil. normalize.
Qed.
Hint Rewrite ilseg_nil_eq : normalize.

Lemma lift2_ilseg_cons: 
 forall s p q, lift2 (ilseg_cons s)  p q =
    EX hry:(int * list int * val),
      match hry with (h,r,y) =>
       !! (s = h::r) &&
       (local (lift2 ptr_neq p q) &&
       (lift2 (field_mapsto Share.top list_struct list_data) p (lift0 (Vint h)) *
        lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) *
        |> lift2 (ilseg r) (lift0 y) q))
     end.
Proof.
 intros.
 unfold ilseg_cons, lseg_cons, lift2. extensionality rho. simpl.
 unfold local, lift1. unfold ptr_neq.
 unfold ilseg.
 apply pred_ext; normalize.
 destruct s; symmetry in H0; inv H0.
 apply exp_right with (i, s, y). normalize.
 destruct h as [[h r] y]. normalize.
 apply exp_right with (Vint h). normalize. apply exp_right with (map Vint r).
 normalize. apply exp_right with y. normalize.
 apply andp_right.
 forget (field_mapsto Share.top list_struct P.i_h (p rho) (Vint h) ) as A.
 forget (|>lseg P.t_listptr (map Vint r) y (q rho)) as B.
 erewrite (field_mapsto_typecheck_val); try reflexivity.
 normalize.
 apply prop_right.
 replace P.t_listptr with (type_of_field
         (unroll_composite_fields list_structid list_struct
            (Fcons list_data list_dtype
               (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)))
         P.i_t); auto.
 type_of_field_tac.
 normalize.
Qed.

(* Hint Rewrite lift2_ilseg_cons : normalize. *)

Definition sumlist_spec :=
 DECLARE P.i_sumlist
  WITH contents 
  PRE [ P.i_p : P.t_listptr]  lift2 (ilseg contents) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_int ]  local (lift1 (eq (Vint (fold_right Int.add Int.zero contents))) retval).

Definition reverse_spec :=
 DECLARE P.i_reverse
  WITH contents : list int
  PRE  [ P.i_p : P.t_listptr ] lift2 (ilseg contents) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_listptr ] lift2 (ilseg (rev contents)) retval (lift0 nullval).

Definition main_spec :=
 DECLARE P.i_main
  WITH u : unit
  PRE  [] main_pre P.prog u
  POST [ P.t_int ] main_post P.prog u.

Definition main_spec' := (P.i_main, mk_funspec (nil, P.t_int) _ (main_pre P.prog) (main_post P.prog)).

Definition Vprog : varspecs := (P.i_three, Tarray P.t_list 3 noattr)::nil.

Definition Gprog : funspecs := 
   sumlist_spec :: reverse_spec :: main_spec::nil.

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Definition sumlist_Inv (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL ((* lift1 (tc_val P.t_int) (eval_id P.i_s); *)
                                     lift1 (partial_sum contents cts) (eval_id P.i_s)) 
            SEP (TT * lift2 (ilseg cts) (eval_id P.i_t) (lift0 nullval))).

Ltac start_function :=
match goal with |- semax_body _ _ _ ?spec => try unfold spec end;
match goal with |- semax_body _ _ _ (pair _ (mk_funspec _ _ ?Pre _)) =>
  match Pre with fun i => _ => intro i end;
  simpl fn_body; simpl fn_params; simpl fn_return;
  canonicalize_pre
 end.


Opaque sepcon.
Opaque emp.
Opaque andp.


Ltac go_lower' := let rho := fresh "rho" in intro rho; normalize.


Lemma body_sumlist: semax_body Vprog Gprog P.f_sumlist sumlist_spec.
Proof.
start_function.
forward.
forward.
forward_while (sumlist_Inv contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P.i_s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with contents.
go_lower'.
rewrite H0. rewrite H1. unfold partial_sum.
rewrite Int.add_zero_l. normalize.
rewrite sepcon_comm.
apply sepcon_TT.
(* Prove that loop invariant implies typechecking condition *)
intro; apply TT_right.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold sumlist_Inv.
go_lower'. intros.
unfold partial_sum in H0;  rewrite H0.
rewrite (typed_false_ptr H).
normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1.
autorewrite with normalize.
apply extract_exists_pre; intro cts.
autorewrite with normalize.
replace_in_pre (ilseg cts) (ilseg_cons cts).
rewrite ilseg_nonnull; auto.
rewrite lift2_ilseg_cons.
normalizex. intros [[h r] y].
normalizex. subst cts.
simpl list_data; simpl list_link.
forward. normalize.
forward.  intro old_t.
forward.
(* Prove postcondition of loop body implies loop invariant *)
normalize.
intro x; unfold sumlist_Inv.
 apply exp_right with r.
go_lower'.
simpl in H0.
autorewrite with normalize in H0.
rewrite H0.
unfold partial_sum in *.
simpl in H4. rewrite H4. clear H4. rewrite H1. clear H1.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
destruct (tc_val_extract_int _ _ _ _ H1) as [n ?].
rewrite H4 in *.
destruct x; inv H0.
simpl. rewrite (Int.add_assoc i h). normalizex.
rewrite <- (sepcon_comm TT).
repeat rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
normalize.
(* After the loop *)
forward.
go_lower'. simpl opt2list. simpl eval_exprlist. normalize.
apply andp_right; normalize.
eapply tc_eval_id_i; eauto.
rewrite H0.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
destruct (eval_id P.i_s rho); inv H1; auto.
unfold retval; simpl. normalize.
Qed.

Definition reverse_Inv (contents: list int) : assert :=
          (EX cts1: list int, EX cts2 : list int,
            PROP (contents = rev cts1 ++ cts2) 
            LOCAL ()
            SEP (lift2 (ilseg cts1) (eval_id P.i_w) (lift0 nullval) *
                   lift2 (ilseg cts2) (eval_id P.i_v) (lift0 nullval))).

Lemma body_reverse: semax_body Vprog Gprog P.f_reverse reverse_spec.
Proof.
start_function.
forward.
go_lower'. simpl. normalize.
forward.
forward_while (reverse_Inv contents)
         (PROP() LOCAL () SEP( lift2 (ilseg (rev contents)) (eval_id P.i_w) (lift0 nullval))).
(* precondition implies loop invariant *)
unfold reverse_Inv.
go_lower.
apply exp_right with nil.
apply exp_right with contents.
normalize.
rewrite H0. rewrite H1.
simpl; normalize. 
(* loop invariant implies typechecking of loop condition *)
normalizex.
(* loop invariant (and not loop condition) implies loop postcondition *)
unfold reverse_Inv.
go_lower. intro cts2.
rewrite (typed_false_ptr H). 
normalize.
rewrite <- app_nil_end. rewrite rev_involutive. auto.
(* loop body preserves invariant *)
unfold reverse_Inv at 1.
normalize.
apply extract_exists_pre; intro cts.
normalize.
apply extract_exists_pre; intro cts2.
normalizex.
subst.
replace_in_pre (ilseg cts2) (ilseg_cons cts2).
   rewrite (ilseg_nonnull cts2) by auto. auto.
rewrite lift2_ilseg_cons.
normalizex. intros [[h r] y].
normalizex; subst cts2.
simpl list_data; simpl list_link.
forward. normalize.
forward. normalize.
forward. intro old_w.
forward.
intros.
unfold reverse_Inv.
go_lower.
apply exp_right with (h::cts).
apply exp_right with r.
normalize.
simpl. rewrite app_ass.
simpl.
normalize.
rewrite (ilseg_unroll (h::cts)).
apply derives_trans with (ilseg_cons (h :: cts) (eval_id P.i_w rho) nullval *
    ilseg r (eval_id P.i_v rho) nullval).
unfold ilseg_cons, lseg_cons.
normalize. apply exp_right with (Vint h).
normalize. apply exp_right with (map Vint cts).
normalize. apply exp_right with old_w.
normalize. rewrite H0.
simpl list_data; simpl list_link.
repeat rewrite <- sepcon_assoc.
erewrite (field_mapsto_typecheck_val _ _ _ _ _ P.i_list _  noattr); [ | reflexivity].
type_of_field_tac.
normalize.
assert (eval_cast P.t_listptr P.t_listptr old_w = old_w)
  by (destruct old_w ; inv H3; simpl; auto).
rewrite H4 in *.
normalize.
repeat pull_right (field_mapsto Share.top P.t_list P.i_t (eval_id P.i_w rho) old_w).
apply sepcon_derives; auto.
repeat pull_right (field_mapsto Share.top list_struct P.i_h (eval_id P.i_w rho) (Vint h)).
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
apply now_later.
apply sepcon_derives; auto.
apply orp_right2; auto.
(* after the loop *)
forward.
go_lower.
simpl.
apply andp_right; normalize.
apply prop_right.
eapply tc_eval_id_i; eauto.
unfold retval; normalize.
Qed.


Lemma body_main:  semax_body Vprog Gprog P.f_main main_spec.
Proof.
start_function.
replace (main_pre P.prog u) with 
   (lift2 (ilseg (map Int.repr (1::2::3::nil)))
       (eval_expr (Ecast
           (Eaddrof (Evar P.i_three (Tarray P.t_list 3 noattr))
              (Tpointer (Tarray P.t_list 3 noattr) noattr)) P.t_listptr)) (lift0 nullval))
 by admit. (* must improve global var specifications *)
normalize.
forward.
go_lower. unfold F,x.
instantiate (2:= (Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)).
instantiate (1:=nil).
normalize.
go_lower. unfold x. apply andp_right.
apply prop_right. hnf. simpl. repeat split; hnf; auto.
simpl. normalize.
unfold x,F in *; clear x F.
apply extract_exists_pre; normalize.

forward.
go_lower. 
unfold x,F.
instantiate (2:= (Int.repr 3 :: Int.repr 2 :: Int.repr 1 :: nil)).
instantiate (1:=nil).
normalize.
go_lower.
repeat apply andp_right; try apply prop_right.
repeat split; simpl; hnf; auto.
normalize.
apply extract_exists_pre; intro old.
normalize. clear old.
forward.
go_lower.
eapply tc_eval_id_i; eauto.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.

