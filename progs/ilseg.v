Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import Ctypes.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import progs.field_mapsto.
Require Import progs.assert_lemmas.
Require Import progs.client_lemmas.
Require Import progs.list.
Require Import Clightdefs.
Require  progs.test1.  Module P := progs.test1.
Local Open Scope logic.

Definition t_listptr := tptr P.t_struct_list.

Instance t_list_spec: listspec t_listptr.
Proof.
econstructor.
reflexivity.
intro Hx; inv Hx.
intros.
unfold unroll_composite; simpl.
reflexivity.
econstructor; simpl; reflexivity.
Defined.

Definition ilseg (sh: share) (s: list int) := lseg t_listptr sh (map Vint s).

Definition ilseg_nil (l: list  int) x z : mpred := !! (ptr_eq x z) && !! (l=nil) && emp.
Definition ilseg_cons (sh: share) (s: list int) := lseg_cons t_listptr sh (map Vint s).

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
   typecheck_val p t_listptr = true -> 
    (ilseg sh s p p = !!(s=nil) && emp).
Proof. intros. unfold ilseg. rewrite lseg_eq; auto. f_equal. f_equal.
 apply prop_ext. destruct s; simpl; intuition congruence.
Qed.
Hint Rewrite ilseg_eq : normalize.

Lemma ilseg_nonnull:
  forall sh s v,
      typed_true t_listptr v ->
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
 forget (field_mapsto sh list_struct P._h (p rho) (Vint h) ) as A.
 forget (|>lseg t_listptr sh (map Vint r) y (q rho)) as B.
 erewrite (field_mapsto_typecheck_val); try reflexivity.
 normalize.
 apply prop_right.
 replace t_listptr with (type_of_field
         (unroll_composite_fields list_structid list_struct
            (Fcons list_data list_dtype
               (Fcons list_link (Tcomp_ptr list_structid noattr) Fnil)))
         P._t); auto.
 type_of_field_tac.
 normalize.
Qed.

Lemma unfold_ilseg_cons:
   forall P Q1 Q R e sh s,
      local Q1 &&
      PROPx P (LOCALx Q (SEPx (lift2 (ilseg sh s) e (lift0 nullval) :: R))) |-- 
                        local (lift1 (typed_true (tptr P.t_struct_list)) e) ->
      local Q1 && PROPx P (LOCALx Q (SEPx (lift2 (ilseg sh s) e (lift0 nullval) :: R))) |--
     EX hry: int * list int * val,
      match hry with (h,r,y) => 
       !! (s=h::r) &&
      PROPx P (LOCALx Q 
        (SEPx (lift2 (field_mapsto sh list_struct P._h) e (lift0 (Vint h)) ::
                  lift2 (field_mapsto sh list_struct P._t) e (lift0 y) ::
                  |> lift2 (ilseg sh r) (lift0 y) (lift0 nullval) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(local Q1 && PROPx P (LOCALx Q (SEPx (lift2 (ilseg_cons sh s) e (lift0 nullval) :: R)))).
apply derives_trans with
(local Q1 && local (lift1 (typed_true (tptr P.t_struct_list)) e) &&
 PROPx P (LOCALx Q (SEPx (lift2 (ilseg sh s) e (lift0 nullval) :: R)))).
apply andp_right; auto.
apply andp_right; auto.
apply andp_left1; auto.
apply andp_left2; auto.
clear H.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
normalize.
rewrite ilseg_nonnull by auto.
auto.
rewrite lift2_ilseg_cons.
clear.
intro rho; unfold PROPx,LOCALx,SEPx,local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
normalize.
apply exp_right with x;
destruct x as [[h r] y].
normalize.
cancel.
Qed.

Lemma semax_ilseg_nonnull:
  forall Delta P Q sh s e R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (lift2 (ilseg sh s) e (lift0 nullval) :: R))) |-- 
                        local (lift1 (typed_true (tptr P.t_struct_list)) e)  ->
  (forall (h: int) (r: list int) (y: val), s=h::r ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (lift2 (field_mapsto sh list_struct P._h) e (lift0 (Vint h)) ::
                  lift2 (field_mapsto sh list_struct P._t) e (lift0 y) ::
                  |> lift2 (ilseg sh r) (lift0 y) (lift0 nullval) ::
                  R)))) c Post) ->
  semax Delta (PROPx P (LOCALx Q (SEPx (lift2 (ilseg sh s) e (lift0 nullval) :: R)))) c Post.
Proof.
intros.
eapply semax_pre;  [apply unfold_ilseg_cons | ].
eapply derives_trans; [ | apply H].
normalize.
apply extract_exists_pre; intros [[h r] y].
apply semax_extract_prop; intro; auto.
Qed.
