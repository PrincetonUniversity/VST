Load loadpath.
Require Import veric.SeparationLogic.
Require Import Coqlib compositional_compcert.Coqlib2.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.

Local Open Scope logic.

Lemma mapsto_isptr:
  forall sh t v1 v2,
   mapsto sh t v1 v2 = !! (denote_tc_isptr v1) && mapsto sh t v1 v2.
Proof.
intros; unfold mapsto.
destruct (access_mode t); normalize.
destruct v1; normalize.
Qed.

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

Definition field_storable (sh: Share.t) (t1: type) (fld: ident) (v1: val) : mpred :=
 match v1, t1 with
  | Vptr l ofs, Tstruct id fList  att =>
    let fList' := unroll_composite_fields id t1 fList in
    let t2 := type_of_field fList' fld in
     match field_offset fld fList',  access_mode t2 with
     | Errors.OK delta, By_value ch => 
          !!(type_is_volatile t2 = false) &&
           EX v2:val,
           address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)  (l, Int.unsigned (Int.add ofs (Int.repr delta)))
     | _, _ => FF
     end
  | _, _  => FF
  end.

Lemma field_mapsto_storable:
  forall sh t1 fld v1 v2, field_mapsto sh t1 fld v1 v2 |-- field_storable sh t1 fld v1.
Proof.
intros.
unfold field_mapsto, field_storable.
destruct v1; auto.
destruct t1; auto.
destruct (field_offset fld (unroll_composite_fields i0 (Tstruct i0 f a) f)); auto.
destruct (access_mode
    (type_of_field (unroll_composite_fields i0 (Tstruct i0 f a) f) fld)); auto.
normalize.
apply exp_right with v2; normalize.
Qed.

Lemma mapsto_field_storable:
  forall ch v1 v1' sh ofs t structid fld fields,
  access_mode
        (type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld) = By_value ch ->
  access_mode t = By_value ch ->
  field_offset fld fields = Errors.OK ofs ->
  v1' = offset_val v1 (Int.repr ofs) ->
  (type_is_volatile
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = false) ->
  (EX v2:val, mapsto sh t v1' v2) = field_storable sh (Tstruct structid fields noattr) fld v1.
Proof.
intros.
unfold field_storable, mapsto.
rewrite H0.
subst v1'.
rewrite  H.
rewrite field_offset_unroll. rewrite H1. rewrite H3.
destruct v1;
 try solve [apply pred_ext; [apply exp_left; auto | apply FF_left]].
rewrite prop_true_andp by auto.
f_equal.
Qed.

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

Lemma field_storable_nonnull:  forall t fld sh x, 
     field_storable sh t fld x = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_storable sh t fld x.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_storable.
unfold Cop.bool_val.
destruct x; normalize.
Qed.

Lemma field_mapsto_nonnull:  forall t fld sh x y, 
     field_mapsto sh t fld x y = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_mapsto sh t fld x y.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_mapsto.
unfold Cop.bool_val.
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

Lemma mapsto_field_mapsto:
  forall ch v1 v1' v2 sh ofs t structid fld fields,
  access_mode
        (type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld) = By_value ch ->
  access_mode t = By_value ch ->
  field_offset fld fields = Errors.OK ofs ->
  v1' = offset_val v1 (Int.repr ofs) ->
  (typecheck_val v2
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = true)  ->
  (type_is_volatile
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = false) ->
  mapsto sh t v1' v2 = field_mapsto sh (Tstruct structid fields noattr) fld v1 v2.
Proof.
intros.
unfold field_mapsto, mapsto.
rewrite H0.
subst v1'.
destruct v1; simpl; normalize.          
rewrite field_offset_unroll. rewrite H1. rewrite H.
normalize.
Qed.

Lemma mapsto_field_mapsto':
  forall ch v1 v1' v2 sh ofs t structid fld fields,
  access_mode
        (type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld) = By_value ch ->
  access_mode t = By_value ch ->
  field_offset fld fields = Errors.OK ofs ->
  v1' = offset_val v1 (Int.repr ofs) ->
  (typecheck_val v2
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = true)  ->
  (type_is_volatile
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = false) ->
  mapsto sh t v1' v2 |-- field_mapsto sh (Tstruct structid fields noattr) fld v1 v2.
Proof.
intros.
erewrite mapsto_field_mapsto; eauto.
Qed.


Lemma field_mapsto_isptr: forall t fld sh x y,
  field_mapsto sh t fld x y = !!(denote_tc_isptr x) && field_mapsto sh t fld x y.
Proof.
unfold field_mapsto; intros.
destruct x; simpl; normalize.
Qed.


Ltac mapsto_field_mapsto_tac :=  
 eapply mapsto_field_mapsto'; 
  try unfold field_offset;  simpl;  
  repeat rewrite if_false by (intro Hx; inv Hx); repeat rewrite if_true by auto; 
  try reflexivity; try solve [normalize].


Global Opaque field_mapsto.

Lemma field_mapsto_force_ptr: 
   forall sh t fld v, field_mapsto sh t fld (force_ptr v) = field_mapsto sh t fld v.
Proof.
intros.
extensionality y. rewrite field_mapsto_nonnull.
destruct v; simpl; normalize.
Qed.
Hint Rewrite field_mapsto_force_ptr : normalize.

