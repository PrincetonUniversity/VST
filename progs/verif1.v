Load loadpath.
Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
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

Definition ilseg (sh: share) (s: list int) := lseg P.t_listptr sh (map Vint s).

Definition ilseg_nil (l: list  int) x z : mpred := !! (ptr_eq x z) && !! (l=nil) && emp.
Definition ilseg_cons (sh: share) (s: list int) := lseg_cons P.t_listptr sh (map Vint s).

Lemma ilseg_unroll: forall sh l x z , 
    ilseg sh l x z = ilseg_nil l x z || ilseg_cons sh l x z.
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

Lemma ilseg_eq: forall sh s p, 
   typecheck_val p P.t_listptr = true -> 
    (ilseg sh s p p = !!(s=nil) && emp).
Proof. intros. unfold ilseg. rewrite lseg_eq; auto. f_equal. f_equal.
 apply prop_ext. destruct s; simpl; intuition congruence.
Qed.
Hint Rewrite ilseg_eq : normalize.

Lemma ilseg_nonnull:
  forall sh s v,
      typed_true P.t_listptr v ->
     ilseg sh s v nullval = ilseg_cons sh s v nullval.
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

Lemma ilseg_nil_eq: forall sh p q, ilseg sh nil p q = !! (ptr_eq p q) && emp.
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
 forall sh s p q, lift2 (ilseg_cons sh s)  p q =
    EX hry:(int * list int * val),
      match hry with (h,r,y) =>
       !! (s = h::r) &&
       (local (lift2 ptr_neq p q) &&
       (lift2 (field_mapsto sh list_struct list_data) p (lift0 (Vint h)) *
        lift2 (field_mapsto sh list_struct list_link) p (lift0 y) *
        |> lift2 (ilseg sh r) (lift0 y) q))
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
 forget (field_mapsto sh list_struct P.i_h (p rho) (Vint h) ) as A.
 forget (|>lseg P.t_listptr sh (map Vint r) y (q rho)) as B.
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

Definition sumlist_spec :=
 DECLARE P.i_sumlist
  WITH sh_contents 
  PRE [ P.i_p : P.t_listptr]  lift2 (ilseg (fst sh_contents) (snd sh_contents)) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_int ]  local (lift1 (eq (Vint (fold_right Int.add Int.zero (snd sh_contents)))) retval).

Definition reverse_spec :=
 DECLARE P.i_reverse
  WITH sh_contents : share * list int
  PRE  [ P.i_p : P.t_listptr ] !! writable_share (fst sh_contents) &&
        lift2 (ilseg (fst sh_contents) (snd sh_contents)) (eval_id P.i_p) (lift0 nullval)
  POST [ P.t_listptr ] lift2 (ilseg (fst sh_contents) (rev (snd sh_contents))) retval (lift0 nullval).

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

Definition sumlist_Inv (sh: share) (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL (lift1 (partial_sum contents cts) (eval_id P.i_s)) 
            SEP (TT * lift2 (ilseg sh cts) (eval_id P.i_t) (lift0 nullval))).

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

Lemma body_sumlist: semax_body Vprog Gprog P.f_sumlist sumlist_spec.
Proof.
start_function.
destruct sh_contents as [sh contents]. simpl @fst; simpl @snd.
forward.
forward.
forward_while (sumlist_Inv sh contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P.i_s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv, partial_sum.
apply exp_right with contents.
go_lower.
rewrite H0. rewrite H1.
rewrite Int.add_zero_l. normalize.
rewrite sepcon_comm.
apply sepcon_TT.
(* Prove that loop invariant implies typechecking condition *)
intro; apply TT_right.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold sumlist_Inv, partial_sum.
go_lower. intros.  rewrite H0.
rewrite (typed_false_ptr H).
normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1.
autorewrite with normalize.
apply extract_exists_pre; intro cts.
autorewrite with normalize.
replace_in_pre (ilseg sh cts) (ilseg_cons sh cts).
rewrite ilseg_nonnull; auto.
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
go_lower.
autorewrite with normalize in H0.
rewrite H0. rewrite H4. clear H4. rewrite H1. clear H1.
assert (H1: tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
destruct (tc_val_extract_int _ _ _ _ H1) as [n H4].
rewrite H4 in *.
destruct x; inv H0.
simpl. rewrite (Int.add_assoc i h). normalizex.
rewrite <- (sepcon_comm TT).
repeat rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
normalize.
(* After the loop *)
forward.
go_lower.
apply andp_right; normalize.
eapply tc_eval_id_i; eauto.
rewrite H0.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
destruct (eval_id P.i_s rho); inv H1; auto.
unfold retval; simpl. normalize.
Qed.

Definition reverse_Inv (sh: share) (contents: list int) : assert :=
          (EX cts1: list int, EX cts2 : list int,
            PROP (contents = rev cts1 ++ cts2) 
            LOCAL ()
            SEP (lift2 (ilseg sh cts1) (eval_id P.i_w) (lift0 nullval) *
                   lift2 (ilseg sh cts2) (eval_id P.i_v) (lift0 nullval))).

Lemma body_reverse: semax_body Vprog Gprog P.f_reverse reverse_spec.
Proof.
start_function.
destruct sh_contents as [sh contents]. simpl @fst; simpl @snd.
normalizex. rename H into WS.
forward.
go_lower.
forward.
forward_while (reverse_Inv sh contents)
         (PROP() LOCAL () SEP( lift2 (ilseg sh (rev contents)) (eval_id P.i_w) (lift0 nullval))).
(* precondition implies loop invariant *)
unfold reverse_Inv.
go_lower.
apply exp_right with nil. normalize.
apply exp_right with contents. normalize.
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
normalizex. subst contents.
replace_in_pre (ilseg sh cts2) (ilseg_cons sh cts2).
rewrite (ilseg_nonnull sh cts2) by auto. auto.
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
rewrite (ilseg_unroll sh (h::cts)).
apply derives_trans with (ilseg_cons sh (h :: cts) (eval_id P.i_w rho) nullval *
    ilseg sh r (eval_id P.i_v rho) nullval).
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
repeat pull_right (field_mapsto sh P.t_list P.i_t (eval_id P.i_w rho) old_w).
apply sepcon_derives; auto.
repeat pull_right (field_mapsto sh list_struct P.i_h (eval_id P.i_w rho) (Vint h)).
apply sepcon_derives; auto.
rewrite sepcon_comm.
apply sepcon_derives; auto.
apply now_later.
apply sepcon_derives; auto.
apply orp_right2; auto.
(* after the loop *)
forward.
go_lower.
apply andp_right; normalize.
apply prop_right.
eapply tc_eval_id_i; eauto.
unfold retval; normalize.
Qed.


Lemma setup_globals:
  forall rho,  tc_environ (func_tycontext P.f_main Vprog Gprog) rho ->
   main_pre P.prog tt rho
   |-- ilseg Ews (Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)
             (eval_var P.i_three (Tarray P.t_list 3 noattr) rho)
      nullval.
Proof.
 unfold main_pre.
 go_lower.
 simpl.
 destruct (globvar_eval_var (Genv.globalenv P.prog) _ _ P.i_three _ H (eq_refl _) (eq_refl _))
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

Lemma body_main:  semax_body Vprog Gprog P.f_main main_spec.
Proof.
start_function.
normalize.
forward. 
go_lower. unfold F,x.
instantiate (2:= (Ews, Int.repr 1 :: Int.repr 2 :: Int.repr 3 :: nil)).
instantiate (1:=nil).
rewrite prop_true_andp by (compute; intuition).
rewrite prop_true_andp by auto.
destruct u; simpl. normalize.
repeat eval_cast_simpl.
apply setup_globals; auto.
unfold x,F in *; clear x F.
apply extract_exists_pre; normalize.
forward.
go_lower. 
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
go_lower.
eapply tc_eval_id_i; eauto.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
unfold prog_funct; simpl prog_defs.
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.

