Require Import veric.SeparationLogic.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Lemma field_offset_rec_unroll:
  forall fields0 fld sid fields n,
    field_offset_rec fld (unroll_composite_fields sid (Tstruct sid fields0 noattr) fields) n =
    field_offset_rec fld fields n.
Proof.
intros. revert n; induction fields; intros; auto.
unfold unroll_composite_fields, field_offset.
simpl. if_tac.
f_equal.
f_equal.
change (alignof (unroll_composite  sid (Tstruct sid fields0 noattr) t) = alignof t).
apply alignof_unroll_composite.
change (field_offset_rec fld  (unroll_composite_fields sid (Tstruct sid fields0 noattr) fields)
             (align n (alignof (unroll_composite sid (Tstruct sid fields0 noattr) t)) 
                          + sizeof (unroll_composite sid (Tstruct sid fields0 noattr) t)) = 
    field_offset_rec fld fields (align n (alignof t) + sizeof t)).
rewrite IHfields.
rewrite alignof_unroll_composite.
rewrite sizeof_unroll_composite.
auto.
Qed.

Lemma field_offset_unroll:
  forall fields0 fld sid fields,
    field_offset fld (unroll_composite_fields sid (Tstruct sid fields0 noattr) fields) =
    field_offset fld fields.
Proof.
intros.
apply field_offset_rec_unroll.
Qed.

Fixpoint type_of_field (f: fieldlist) (fld: ident) : type :=
 match f with
 | Fnil => Tvoid
 | Fcons i t fl => if eq_dec i fld then t else type_of_field fl fld
 end.

Definition field_mapsto (sh: Share.t) (t1: type) (fld: ident) (v1 v2: val) : mpred :=
 match v1, t1 with
  | Vptr l ofs, Tstruct id fList  att =>
    let fList' := unroll_composite_fields id t1 fList in
    let t2 := type_of_field fList' fld in
     match field_offset fld fList',  access_mode t2 with
     | Errors.OK delta, By_value ch => 
          !! (typecheck_val v2 t2 = true) && !!(type_is_volatile t2 = false) &&
           address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)  (l, Int.unsigned (Int.add ofs (Int.repr delta)))
     | _, _ => FF
     end
  | _, _  => FF
  end.

Lemma field_mapsto_typecheck_val:
  forall t fld sh x y id fList att, 
     t = Tstruct id fList att ->
     field_mapsto sh t fld x y = 
               !! (typecheck_val y (type_of_field (unroll_composite_fields id t fList) fld) = true) && field_mapsto sh t fld x y.
Proof.
intros. subst.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
destruct x; normalize.
destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList)); normalize.
destruct (access_mode
    (type_of_field (unroll_composite_fields id (Tstruct id fList att) fList) fld)); normalize.
Qed.

Lemma field_mapsto_nonnull:  forall t fld sh x y, 
     field_mapsto sh t fld x y = 
               !! (bool_val x (Tpointer t noattr) = Some true) && field_mapsto sh t fld x y.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
unfold bool_val.
destruct x; normalize.
Qed.

Lemma field_offset_exists1: 
  forall sid t fields fld,
    type_of_field (unroll_composite_fields sid t fields) fld <> Tvoid ->
    exists n, field_offset fld fields = Errors.OK n.
intros.
unfold field_offset.
forget 0 as k. revert k.
induction fields; intro k; simpl in H. congruence.
destruct (eq_dec i fld). subst i.
econstructor; simpl. rewrite if_true by auto.
reflexivity.
simpl. rewrite if_false by auto.
destruct (IHfields H (align k (alignof t0) + sizeof t0)).
eauto.
Qed.


Lemma field_mapsto_access_mode:
  forall sh v t fld v' id fList att,
   t = Tstruct id fList att ->
  field_mapsto sh t fld v v' = 
   !! (exists ch, access_mode (type_of_field (unroll_composite_fields id t fList) fld) = By_value ch) 
           && field_mapsto sh t fld v v'.
Proof.
intros. subst.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
destruct v; normalize.
destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList)); normalize.
case_eq (access_mode
    (type_of_field
       (unroll_composite_fields id (Tstruct id fList att) fList) fld)); intros; normalize.
apply prop_right; eauto.
Qed.

Import SequentialClight.SeqC.CSL.


Lemma splice_top_top: Share.splice Share.top Share.top = Share.top.
Proof.
unfold Share.splice.
unfold Share.Lsh, Share.Rsh.
case_eq (Share.split Share.top); intros L R ?.
simpl.
do 2 rewrite Share.rel_top1.
erewrite Share.split_together; eauto.
Qed.


(* move this elsewhere, and by the way it generalizes the same-named lemma
  in veric/semax_straight.v *)
Lemma cast_exists : forall Delta e2 t rho 
(TC: typecheck_environ rho Delta = true), 
denote_tc_assert (typecheck_expr Delta e2) rho ->
denote_tc_assert (isCastResultType (typeof e2) t t e2)
  rho ->
sem_cast (eval_expr e2 rho) (typeof e2) t =
Some (force_val (sem_cast (eval_expr e2 rho) (typeof e2) t)).
Proof.
intros. 
assert (exists v, sem_cast (eval_expr e2 rho) (typeof e2) t= Some v).

apply expr_lemmas.typecheck_expr_sound in H.
rename t into t0.
remember (typeof e2); remember (eval_expr e2 rho). 
unfold sem_cast. unfold classify_cast.
Transparent Float.intoffloat.
Transparent Float.intuoffloat.
destruct t; destruct v; destruct t0; simpl in *;
try congruence; try contradiction; eauto;
try solve [
unfold Float.intoffloat, Float.intuoffloat; repeat invSome;
inversion2 H1 H0; hnf in H2,H3; rewrite H3; rewrite Zle_bool_rev; rewrite H2;
simpl; eauto];
try solve [
try destruct i; try destruct s; try destruct i0; try destruct i1; try destruct s0; eauto |

destruct i; destruct s; unfold lift2 in *; try solve[simpl in *; 
  unfold lift2,lift1 in *;  expr_lemmas.unfold_tc_denote; destruct H0; 
try rewrite <- Heqv in *; 
unfold Float.intoffloat; 
destruct (Float.Zoffloat f0); try contradiction;
try rewrite H0; try rewrite H1; simpl; eauto | 
simpl in *;  unfold Float.intuoffloat; destruct H0;
expr_lemmas.unfold_tc_denote; try rewrite <- Heqv in *; destruct (Float.Zoffloat f0);
try rewrite H0; try rewrite H1; simpl; eauto; try contradiction] |

try destruct i0; try destruct i1; destruct s; simpl in *; try contradiction; try rewrite H; eauto ].

destruct i; destruct s; unfold lift2 in *;
simpl in *; unfold lift2,lift1 in *;
unfold Float.intoffloat, Float.intuoffloat;
try (
destruct H0 as [H0 H1]; hnf in H0,H1; rewrite <- Heqv in *;
destruct (Float.Zoffloat f0); try contradiction;
hnf in H0,H1; rewrite H0; rewrite expr_lemmas.Zle_bool_rev; rewrite H1;
simpl; eauto);
simpl; eauto.

auto.
Opaque Float.intoffloat.
Opaque Float.intuoffloat.

destruct H1. rewrite H1. auto.
Qed. 

(* Admitted:  after Joey checks in his revision of environments,
 move this definition (and similar ones in progs/assert_lemmas
  into expr.v, and use it in the definition of eval_expr *)
Definition eval_cast (t t': type) (v: val) : val := force_val (sem_cast v t t').
Definition tc_val (t: type) (v: val) : Prop := typecheck_val v t = true.

Lemma typecheck_val_eval_cast: 
  forall t2 e2 rho Delta,
      typecheck_environ rho Delta = true ->
      denote_tc_assert (typecheck_expr Delta e2) rho ->
      denote_tc_assert (isCastResultType (typeof e2) t2 t2 e2) rho ->
      typecheck_val (eval_cast (typeof e2) t2 (eval_expr e2 rho)) t2 = true.
Proof. intros ? ? ? ? H2 H5 H6.
assert (H7 := cast_exists _ _ _ _ H2 H5 H6).
assert (H8 := expr_lemmas.typecheck_expr_sound _ _ _ H2 H5).
clear - H7 H6 H8.
revert H7; case_eq (sem_cast (eval_expr e2 rho) (typeof e2) t2); intros; inv H7.
unfold eval_cast. rewrite H. simpl.
case_eq (eval_expr e2 rho); intros; rename H0 into H99;
 destruct t2; inv H8; inv H; simpl; auto;
hnf in H6; try contradiction; rewrite H99 in *;
destruct (typeof e2); inv H2; inv H1; auto;
try (unfold sem_cast in H0; simpl in H0;
      destruct i0; simpl in*; destruct s; inv H0; simpl; auto).
simpl in *. unfold lift1 in H6. rewrite H99 in *. inv H6. auto.
simpl in *. unfold isCastResultType in H6. simpl in H6.
unfold sem_cast in H0. 
simpl in H0.
destruct i; simpl in*; destruct s; try destruct f; inv H0; simpl; auto;
invSome; simpl; auto.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
unfold lift1, denote_tc_iszero in H6; rewrite H99 in *; contradiction.
Qed.

Lemma field_mapsto_offset:
  forall sh sid fields fld b i v ch,
  access_mode (type_of_field
        (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld) = By_value ch ->        
  field_mapsto sh (Tstruct sid fields noattr) fld (Vptr b i) v |--
  match field_offset fld fields with
  | Errors.OK delta => 
     address_mapsto ch v (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)
            (b, Int.unsigned (Int.add i (Int.repr delta)))
  | _ => FF
  end.
Proof.
unfold field_mapsto; simpl; intros.
rewrite H.
case_eq (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields noattr) fields)); intros.
2: rewrite field_offset_unroll in H0; rewrite H0; auto.
normalize.
rewrite field_offset_unroll in H0.
rewrite H0.
auto.
Qed.

Global Opaque field_mapsto.

