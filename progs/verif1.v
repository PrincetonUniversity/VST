Require Import msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import compcert.Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
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

Lemma lift2_ilseg_cons: 
 forall s p q, lift2 (ilseg_cons s)  p q =
    local (lift2 ptr_neq p q) &&
    EX h:int, EX r: list int, EX y: val,
      !! (s = h::r) &&
      lift2 (field_mapsto Share.top list_struct list_data) p (lift0 (Vint h)) *
      lift2 (field_mapsto Share.top list_struct list_link) p (lift0 y) *
      |> lift2 (ilseg r) (lift0 y) q.
Proof.
 intros.
 unfold ilseg_cons, lseg_cons, lift2. extensionality rho. simpl.
 unfold local, lift1. unfold ptr_neq. f_equal.
 unfold ilseg.
 apply pred_ext; normalize.
 intros. destruct s; inv H. apply exp_right with i. apply exp_right with s.
 apply exp_right with x1. normalize.
 intros. apply exp_right with (Vint x). apply exp_right with (map Vint x0).
 apply exp_right with x1. normalize.
 apply andp_right; auto.
 forget (field_mapsto Share.top list_struct P.i_h (p rho) (Vint x) ) as A.
 forget (|>lseg P.t_listptr (map Vint x0) x1 (q rho)) as B.
 erewrite (field_mapsto_typecheck_val); try reflexivity.
 normalize.
 apply prop_right.
 replace P.t_listptr with (type_of_field
         (unroll_composite_fields list_structid list_struct
            (Fcons list_data list_dtype
               (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)))
         P.i_t); auto.
 type_of_field_tac.
Qed.
Hint Rewrite lift2_ilseg_cons : normalize.

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

Definition main_spec := (P.i_main, mk_funspec (nil, P.t_int) _ (main_pre P.prog) (main_post P.prog)).

Definition Gprog : funspecs := 
   sumlist_spec :: reverse_spec :: main_spec::nil.

Definition partial_sum (contents cts: list int) (v: val) := 
     fold_right Int.add Int.zero contents = Int.add (force_int  v) (fold_right Int.add Int.zero cts).

Definition sumlist_Inv (contents: list int) : assert :=
          (EX cts: list int, 
            PROP () LOCAL ((* lift1 (tc_val P.t_int) (eval_id P.i_s); *)
                                     lift1 (partial_sum contents cts) (eval_id P.i_s)) 
            SEP (TT * lift2 (ilseg cts) (eval_id P.i_t) (lift0 nullval))).

Ltac normalizex :=
  normalize;
  repeat 
  (first [ simpl_tc_expr
         | flatten_sepcon_in_SEP
          | apply semax_extract_PROP_True; [solve [auto] | ]
          | apply semax_extract_PROP; intro
         | extract_prop_in_LOCAL
         | extract_exists_in_SEP
         ]; cbv beta; normalize).

Ltac semax_field_tac1 := 
   eapply semax_load_field'; 
     [ reflexivity 
     | reflexivity 
     | simpl; reflexivity 
     | type_of_field_tac ].

Ltac semax_field_tac :=
match goal with |- semax ?Delta _ (PROPx ?P (LOCALx ?Q (SEPx ?R)))
                  (Ssequence (Sset _ (Efield (Ederef ?e _) ?fld _)) _) _ =>
  apply (semax_pre (PROPx P (LOCALx (tc_expr Delta e :: Q) (SEPx R))));
   [ go_lower 
   | match R with 
     | context [|> lift2 (field_mapsto ?sh ?struct ?fld') ?e' ?v] =>
          let H := fresh "EE" in assert (H: fld'=fld) by reflexivity;
          let n := find_in_list (|> lift2 (field_mapsto sh struct fld') e' v) R
             in focus_SEP n; rewrite (grab_nth_LOCAL 0); simpl nth;
                replace e' with (eval_expr e) by auto;
                rewrite H; clear H
     | context [ lift2 (field_mapsto ?sh ?struct ?fld') ?e' ?v] =>
          let H := fresh "EE" in assert (H: fld'=fld) by reflexivity;
         let n := find_in_list (lift2 (field_mapsto sh struct fld') e' v) R
             in focus_SEP n; rewrite (grab_nth_LOCAL 0); simpl nth;
                replace e' with (eval_expr e) by auto;
                rewrite H; clear H
     end;
     match goal with |- semax _ _ ?P _ _ =>
       let P' := strip1_later P in apply semax_pre0 with (|> P'); [solve [auto 50 with derives] | ]
     end;
   first [eapply semax_seq; [ apply sequential'; semax_field_tac1  
                                          | simpl update_tycon; apply extract_exists_pre
                                          ] 
(* should adjust the "semax_post" in the line below...
           | eapply semax_post; [ | apply sequential'; semax_field_tac1 ]
   *)
         ]
   ]
end; normalizex.

Lemma canon17 : forall (P: Prop) PP QR, prop P && (PROPx PP QR) = PROPx (P::PP) QR.
Proof.
intros. unfold PROPx. simpl. extensionality rho. apply pred_ext; normalize.
Qed.
Hint Rewrite canon17 : canon.

Lemma body_sumlist: semax_body Gprog P.f_sumlist sumlist_spec.
Proof.
intro contents.
simpl fn_body; simpl fn_params; simpl fn_return.
normalize.
canonicalize_pre.         
forward_setx.
forward_setx.
forward_while (sumlist_Inv contents)
    (PROP() LOCAL (lift1 (fun v => fold_right Int.add Int.zero contents = force_int v) (eval_id P.i_s))SEP(TT)).
(* Prove that current precondition implies loop invariant *)
unfold sumlist_Inv.
apply exp_right with contents.
go_lower.
rewrite H0. rewrite H1. simpl. unfold partial_sum.
rewrite Int.add_zero_l. normalize.
rewrite sepcon_comm. apply sepcon_TT.
(* Prove that loop invariant implies typechecking condition *)
normalizex.
(* Prove that invariant && not loop-cond implies postcondition *)
unfold sumlist_Inv.
go_lower.
intros cts ?.
unfold partial_sum in H0;  rewrite H0.
rewrite (typed_false_ptr H).
normalize.
(* Prove that loop body preserves invariant *)
unfold sumlist_Inv at 1.
normalize.
apply extract_exists_pre; intro cts.
normalize.
replace_in_pre (ilseg cts) (ilseg_cons cts).
   rewrite ilseg_nonnull by auto.
   unfold ilseg_cons, lseg_cons.
   normalize. intros h r ? y. destruct cts; inv H3.
   apply exp_right with i; normalize.
   apply exp_right with cts; normalize.
   apply exp_right with y; normalize.
rewrite lift2_ilseg_cons.
normalizex.
intros h r y.
normalizex.
subst cts.

semax_field_tac.
semax_field_tac; intro old_t.

apply sequential; simpl for1_ret_assert.

eapply semax_post;  [ | apply forward_setx; [reflexivity | solve [repeat split; hnf; auto]]];
  cbv beta; normalize.
(* Prove postcondition of loop body implies loop invariant *)
intros ek vl; unfold normal_ret_assert, for1_ret_assert.
normalize.
 intro x; unfold sumlist_Inv.
 apply exp_right with r.
 go_lower. 
 apply andp_right; 
 normalize.
 rewrite H0.
apply prop_right.
unfold partial_sum in *.
simpl in H4.
rewrite H4; clear H4. rewrite <- H1; clear H1.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
assert (exists n, x = Vint n).
clear - H1 H0.
rewrite H0 in H1. clear H0.
destruct x; inv H1. eauto.
destruct H4; subst x.
simpl.
symmetry; apply Int.add_assoc.
repeat rewrite <- sepcon_assoc.
apply sepcon_derives; auto.
normalize.
(* After the loop *)
eapply semax_pre; [ | apply semax_return ].
go_lower.
apply prop_left; intro.
unfold frame_ret_assert.
simpl.
normalize.
apply andp_right; apply prop_right.
eapply tc_eval_id_i; eauto.
unfold retval.
normalize.
rewrite H0.
assert (tc_val P.t_int (eval_id P.i_s rho)) by (eapply tc_eval_id_i; eauto).
clear - H2.
destruct (eval_id P.i_s rho); inv H2; auto.
Qed.


Lemma body_reverse: semax_body Gprog P.f_reverse reverse_spec.
Proof.
intro contents.
simpl.
Admitted.

Lemma body_main:  semax_body Gprog P.f_main main_spec.
Proof.
intro x; destruct x.
simpl.
Admitted.

Lemma all_funcs_correct:
  semax_func Gprog (prog_funct P.prog) Gprog.
Proof.
unfold Gprog, P.prog.
apply semax_func_cons; [ reflexivity | apply body_sumlist | ].
apply semax_func_cons; [ reflexivity | apply body_reverse | ].
apply semax_func_cons; [ reflexivity | apply body_main | ].
apply semax_func_nil.
Qed.




