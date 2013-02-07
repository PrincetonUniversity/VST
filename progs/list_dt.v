Load loadpath.
Require Import Coqlib msl.Coqlib2.
Require Import veric.SeparationLogic.
Require Import progs.field_mapsto.
Require Import progs.client_lemmas.
Require Import progs.assert_lemmas.
Require Import progs.malloc_lemmas.
Require Import Clightdefs.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Class listspec (list_structid: ident) (list_link: ident) :=
  mk_listspec {  
   list_fields: fieldlist;
   list_struct: type := (Tstruct list_structid list_fields noattr);
   list_link_type: (type_of_field
          (unroll_composite_fields list_structid list_struct list_fields)
          list_link) = tptr list_struct
}.

Section LIST.
Context  {list_structid} {list_link} (ls: listspec list_structid list_link).

Definition list_cell sh p v :=
   field_storable sh list_struct list_link p -* typed_mapsto list_struct sh 0 p v.

Definition lseg' (sh: share) := 
  HORec (fun (R: (list (reptype list_struct))*(val*val) -> mpred) (lp: (list (reptype list_struct))*(val*val)) =>
        match lp with
        | (h::hs, (first,last)) =>
                (!! (~ (ptr_eq first last)) && 
                        EX tail:val, 
                           list_cell sh first h
                           * field_mapsto sh list_struct list_link first tail
                           * |> R (hs, (tail, last)))
        | (nil, (first,last)) =>
                 !! (ptr_eq first last) && emp
        end).

Definition lseg  (sh: share) (contents: list (reptype list_struct)) (x y: val) : mpred :=
   lseg' sh (contents, (x,y)).

Lemma lseg_unfold: forall sh contents v1 v2,
    lseg sh contents v1 v2 = 
     match contents with
     | h::t => !! (~ ptr_eq v1 v2) && EX tail: val,
                      list_cell sh v1 h
                      * field_mapsto sh list_struct list_link v1 tail
                      * |> lseg sh t tail v2
     | nil => !! (ptr_eq v1 v2) && emp
     end.
Proof.
 intros. unfold lseg.
 unfold lseg' at 1. rewrite HORec_fold_unfold.
  normalize.
 apply prove_HOcontractive; intros.
 destruct x. destruct l. 
 auto 50 with contractive.
 destruct p.
 auto 50 with contractive.
Qed.

Lemma lseg_eq:
  forall sh l v , 
  typecheck_val v (tptr list_struct) = true ->
    lseg sh l v v = !!(l=nil) && emp.
Proof.
intros.
rewrite (lseg_unfold sh l v v).
destruct l.
f_equal. f_equal.
apply prop_ext; split; intro; auto.
unfold ptr_eq.
unfold typecheck_val in H.
destruct v; simpl in H; try discriminate.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
split; auto. 
unfold Int.cmpu.
rewrite Int.eq_true. auto.
normalize.
replace (r :: l = nil) with False by (apply prop_ext; intuition; congruence).
apply pred_ext; normalize.
contradiction H0.
unfold ptr_eq, typecheck_val in H|-*.
destruct v; inv H; auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
unfold Int.cmpu.
rewrite Int.eq_true. auto.
Qed.



Definition lseg_cons sh (l: list (reptype list_struct)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(reptype list_struct), EX r:list (reptype list_struct), EX y:val, 
             !!(l=h::r  /\ typecheck_val y (tptr list_struct) = true) && 
             list_cell sh x h *
             field_mapsto sh list_struct list_link x y * 
             |> lseg sh r y z.

Lemma lseg_neq:  forall sh l x z , 
  typecheck_val x (tptr list_struct) = true ->
  typecheck_val z (tptr list_struct) = true ->
  ptr_neq x z -> 
    lseg sh l x z = lseg_cons sh l x z.
Proof.
unfold lseg_cons, ptr_neq; intros.
rewrite lseg_unfold at 1; auto.
destruct l.
apply pred_ext; apply derives_extract_prop; intro.
contradiction. clear H2.
apply exp_left; intro h.
apply exp_left; intro r.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H2.
apply pred_ext; apply derives_extract_prop; intro.
clear H2.
apply exp_left; intro tail.
apply andp_right; try apply prop_right; auto.
apply exp_right with r.
apply exp_right with l.
apply exp_right with tail.
repeat rewrite sepcon_andp_prop'; apply andp_right.
rewrite (field_mapsto_typecheck_val list_struct list_link sh x tail list_structid list_fields noattr) by auto.
rewrite list_link_type.
normalize. auto.
apply exp_left; intro h.
apply exp_left; intro r'.
apply exp_left; intro y.
repeat rewrite sepcon_andp_prop'; apply derives_extract_prop; intros [? ?].
inv H3.
apply andp_right.
apply prop_right; auto.
apply exp_right with y.
 auto.
Qed.

Lemma lseg_unroll: forall sh l x z , 
    lseg sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons sh l x z.
Proof.
intros.
rewrite lseg_unfold at 1.
apply pred_ext; destruct l.
normalize.
apply orp_right1; auto.
apply orp_right2.
unfold lseg_cons.
normalize.
apply exp_right with r.
normalize.
apply exp_right with l.
normalize.
apply exp_right with tail.
normalize.
apply andp_right.
erewrite (field_mapsto_typecheck_val list_struct list_link sh x tail); try reflexivity.
rewrite list_link_type.
normalize.
auto.
apply orp_left; normalize.
unfold lseg_cons.
normalize. inv H0.
apply orp_left.
normalize. inv H0.
unfold lseg_cons.
normalize.
intros. symmetry in H0; inv H0.
apply exp_right with x0.
normalize.
Qed.

Lemma ptr_eq_dec:
  forall x z, {ptr_eq x z}+{~ptr_eq x z}.
Proof.
unfold ptr_eq; intros.
destruct x; simpl; auto. destruct z; simpl; auto. destruct (Int.eq i i0); auto.
destruct z; auto. destruct (eq_dec b b0).
subst. destruct (Int.eq i i0); auto. right; intros [? ?]; auto. inv H0.
right; intros [? ?]. contradiction.
Qed.


Lemma lseg_unroll_nonempty1:
   forall p P sh h tail v1 v2,
    ~ ptr_eq v1 v2 ->
    typecheck_val p (tptr list_struct) = true ->
    P |-- list_cell sh v1 h *
             (field_mapsto sh list_struct list_link v1 p *
               lseg sh tail p v2) ->
    P |-- lseg sh (h::tail) v1 v2.
Proof. intros. rewrite lseg_unroll. apply orp_right2. unfold lseg_cons.
  rewrite prop_true_andp by auto.
  apply exp_right with h. apply exp_right with tail. apply exp_right with p.
    rewrite prop_true_andp by auto.
 rewrite sepcon_assoc.
 eapply derives_trans; [ apply H1 | ].
 apply sepcon_derives; auto.
 apply sepcon_derives; auto.
 apply now_later.
Qed.

Lemma lseg_nonnull:
  forall sh s v,
      typed_true (tptr list_struct) v ->
     lseg sh s v nullval = lseg_cons sh s v nullval.
Proof.
intros. subst. 
rewrite lseg_unroll.
apply pred_ext; normalize.
apply orp_left; auto. normalize.
unfold typed_true, strict_bool_val,ptr_eq in *.
destruct v; simpl in *; try contradiction.
rewrite H0 in H. inv H.
apply orp_right2. auto.
Qed.

Lemma lift2_lseg_cons: 
 forall sh s p q, `(lseg_cons sh s)  p q =
    EX hry:(reptype list_struct * list (reptype list_struct) * val),
      match hry with (h,r,y) =>
       !! (s = h::r) &&
       (local (`ptr_neq p q) &&
       (`(list_cell sh) p (`h) *
        `(field_mapsto sh list_struct list_link) p (`y) *
        |> `(lseg sh r) (`y) q))
     end.
Proof.
 intros.
 unfold lseg_cons, ptr_neq; unfold_coerce. extensionality rho. simpl.
 apply pred_ext; normalize.
 apply exp_right with (h, r, y). normalize.
 destruct h as [[h r] y]. normalize.
 apply exp_right with h. apply andp_right; auto.
 apply exp_right with r.
 apply exp_right with y. normalize.
 apply andp_right.
 erewrite (field_mapsto_typecheck_val); [ | reflexivity].
 rewrite list_link_type. normalize. auto.
Qed.

Lemma unfold_lseg_cons:
   forall P Q1 Q R e sh s,
      local Q1 &&
      PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e) ->
      local Q1 && PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R))) |--
     EX hry: reptype list_struct * list (reptype list_struct) * val,
      match hry with (h,r,y) => 
       !! (s=h::r) &&
      PROPx P (LOCALx Q 
        (SEPx (`(list_cell sh) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
                  |> `(lseg sh r) (`y) (`nullval) ::
                  R)))
        end.
Proof.
intros.
apply derives_trans with
(local Q1 && PROPx P (LOCALx Q (SEPx (`(lseg_cons sh s) e (`nullval) :: R)))).
apply derives_trans with
(local Q1 && local (`(typed_true (tptr list_struct)) e) &&
 PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R)))).
apply andp_right; auto.
apply andp_right; auto.
apply andp_left1; auto.
apply andp_left2; auto.
clear H.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue; unfold_coerce; simpl.
normalize.
rewrite lseg_nonnull by auto.
auto.
rewrite lift2_lseg_cons.
clear.
change SEPx with SEPx'.
intro rho; unfold PROPx,LOCALx,SEPx',local,tc_expr,tc_lvalue,lift2,lift1,lift0; simpl.
normalize.
apply exp_right with x;
destruct x as [[h r] y].
normalize.
 repeat rewrite sepcon_assoc.
 auto.
Qed.

Lemma semax_lseg_nonnull:
  forall Delta P Q sh s e R c Post,
   PROPx P (LOCALx (tc_environ Delta :: Q)
            (SEPx (`(lseg sh s) e (`nullval) :: R))) |-- 
                        local (`(typed_true (tptr list_struct)) e)  ->
  (forall (h: reptype list_struct) (r: list (reptype list_struct)) (y: val), s=h::r ->
    semax Delta 
        (PROPx P (LOCALx Q 
        (SEPx (`(list_cell sh) e (`h) ::
                  `(field_mapsto sh list_struct list_link) e (`y) ::
                  |> `(lseg sh r) (`y) (`nullval) ::
                  R)))) c Post) ->
  semax Delta (PROPx P (LOCALx Q (SEPx (`(lseg sh s) e (`nullval) :: R)))) c Post.
Proof.
intros.
eapply semax_pre;  [apply unfold_lseg_cons | ].
eapply derives_trans; [ | apply H].
normalize.
apply extract_exists_pre; intros [[h r] y].
apply semax_extract_prop; intro; auto.
Qed.

Lemma lseg_nil_eq: 
    forall sh p q, lseg sh nil p q = !! (ptr_eq p q) && emp.
Proof. intros.
 rewrite lseg_unroll.
 apply pred_ext.
 apply orp_left. normalize.
 normalize. unfold lseg_cons. normalize. inv H0.
 apply orp_right1. normalize.
Qed.

Definition lseg_cons_right sh (l: list (reptype list_struct)) (x z: val) : mpred :=
        !! (~ ptr_eq x z) && 
       EX h:(reptype list_struct), EX r:list (reptype list_struct), EX y:val, 
             !!(l=r++h::nil)  && 
                       list_cell sh y h *
             field_mapsto sh list_struct list_link y z * 
             |> lseg sh r x y.


Lemma lseg_unroll_right: forall sh l x z , 
    lseg sh l x z = (!! (ptr_eq x z) && !! (l=nil) && emp) || lseg_cons_right sh l x z.
Admitted.

End LIST.

Hint Rewrite @lseg_nil_eq : normalize.

Hint Rewrite @lseg_eq using reflexivity: normalize.



