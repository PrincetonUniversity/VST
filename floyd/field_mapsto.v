Require Import floyd.base.
Require Import floyd.assert_lemmas.

Local Open Scope logic.

Lemma mapsto_mapsto_: forall sh t v v',
   mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto_; intros.
normalize.
unfold mapsto.
destruct (access_mode t); auto.
destruct (type_is_volatile t); try apply FF_left.
destruct v; auto.
apply orp_left.
apply orp_right2.
apply andp_left2.
apply andp_right. apply prop_right; auto.
apply exp_right with v'; auto.
normalize.
apply orp_right2. apply exp_right with v2'.
normalize.
Qed.
Hint Resolve mapsto_mapsto_ : cancel.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh tuint = mapsto sh tint.
Proof.
intros.
extensionality v1 v2.
reflexivity.
Qed.

Lemma mapsto_mapsto__int32:
  forall sh p v s1 s2,
  mapsto sh (Tint I32 s1 noattr) p v |-- mapsto_ sh (Tint I32 s2 noattr) p.
Proof.
intros.
eapply derives_trans; [ apply mapsto_mapsto_ | ].
destruct s1,s2; fold tuint; fold tint; 
  repeat rewrite mapsto_tuint_tint; auto.
Qed.

Hint Extern 2 (mapsto _ _ _ _ |-- mapsto_ _ _ _) =>
   (apply mapsto_mapsto__int32)  : cancel.

Lemma mapsto_mapsto_int32:
  forall sh p v s1 s2,
  mapsto sh (Tint I32 s1 noattr) p v |-- mapsto sh (Tint I32 s2 noattr) p v.
Proof.
intros.
destruct s1,s2; fold tuint; fold tint; 
  repeat rewrite mapsto_tuint_tint; auto.
Qed.

Hint Extern 2 (mapsto _ _ _ _ |-- mapsto _ _ _ _) =>
   (apply mapsto_mapsto_int32)  : cancel.

Lemma tc_val_Vundef:
  forall t, ~ tc_val t Vundef.
Proof. destruct t; intro H; inv H.
Qed.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v, 
             mapsto sh tint v nullval = 
             mapsto sh (tptr t) v nullval.
Proof.
intros.
unfold mapsto.
simpl.
destruct v; auto. f_equal; auto.
f_equal. f_equal.
apply prop_ext; split; intro; hnf in *|-*; auto.
Qed.

Lemma superprecise_mapsto:
  forall sh t v1 v2, 
    v2 <> Vundef -> 
   predicates_sl.superprecise (mapsto sh t v1 v2).
Proof.
intros. rename H into Hv2.
hnf; intros.
unfold mapsto in *;
simpl in H,H0.
destruct (access_mode t); try contradiction.
destruct (type_is_volatile t); try contradiction.
destruct v1; try contradiction.
destruct H as [[_ H]|[Hz [u1 H]]]; try congruence.
destruct H0 as [[_ H0]|[Hz [u2 H0]]]; try congruence.
eapply res_predicates.superprecise_address_mapsto; eauto.
Qed.

Lemma mapsto_isptr:
  forall sh t v1 v2,
   mapsto sh t v1 v2 = !! (isptr v1) && mapsto sh t v1 v2.
Proof.
intros; apply pred_ext; normalize.
apply andp_right; auto.
unfold mapsto.
destruct (access_mode t); normalize.
destruct (type_is_volatile t); normalize.
destruct v1; normalize.
apply prop_right; apply I.
Qed.

Lemma mapsto__isptr:
  forall sh t v1,
   mapsto_ sh t v1 = !! (isptr v1) && mapsto_ sh t v1.
Proof.
intros.
unfold mapsto_. apply mapsto_isptr.
Qed.

Lemma field_offset_rec_unroll:
  forall t_subst fld sid fields n,
    field_offset_rec fld (unroll_composite_fields sid t_subst fields) n =
    field_offset_rec fld fields n.
Proof.
intros. revert n; induction fields; intros; auto.
unfold unroll_composite_fields, field_offset.
simpl. if_tac.
f_equal.
f_equal.
change (alignof (unroll_composite  sid t_subst t) = alignof t).
apply alignof_unroll_composite.
change (field_offset_rec fld (unroll_composite_fields sid t_subst fields)
             (align n (alignof (unroll_composite sid t_subst t)) 
                          + sizeof (unroll_composite sid t_subst t)) = 
    field_offset_rec fld fields (align n (alignof t) + sizeof t)).
rewrite IHfields.
rewrite alignof_unroll_composite.
rewrite sizeof_unroll_composite.
reflexivity.
Qed.

Lemma field_offset_unroll:
  forall t_subst fld sid fields,
    field_offset fld (unroll_composite_fields sid t_subst fields) =
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

Definition field_at (sh: Share.t) (t1: type) (fld: ident) (v2 v1: val) : mpred :=
 match t1 with
  |  Tstruct id fList  att =>
    let fList' := unroll_composite_fields id t1 fList in
    let t2 := type_of_field fList' fld in
     match field_offset fld fList' with
     | Errors.OK delta => 
            !!(type_is_volatile t2 = false) &&
               mapsto sh t2 (offset_val (Int.repr delta) v1) v2
     | _ => FF
     end
  | _  => FF
  end.

Arguments field_at sh t1 fld v2 v1 : simpl never.

Definition field_at_ sh t1 fld := field_at sh t1 fld Vundef.
Arguments field_at_ sh t1 fld v1 : simpl never.


Lemma field_at_field_at_:
  forall sh t1 fld v1 v2, field_at sh t1 fld v2 v1 |-- field_at_ sh t1 fld v1.
Proof.
intros.
unfold field_at_, field_at.
normalize.
destruct t1; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f)); 
  try apply FF_left.
normalize.
unfold mapsto.
destruct (access_mode
    (type_of_field (unroll_composite_fields i (Tstruct i f a) f) fld)); auto.
destruct (type_is_volatile (type_of_field (unroll_composite_fields i (Tstruct i f a) f) fld)); try apply FF_left.
destruct (offset_val (Int.repr z) v1); auto.
apply orp_left; normalize.
apply orp_right2.
apply exp_right with v2; normalize.
apply orp_right2.
apply exp_right with v2'; normalize.
Qed.

Hint Resolve field_at_field_at_: cancel.

Lemma offset_val_force_ptr:
  offset_val Int.zero = force_ptr.
Proof. extensionality v. destruct v; try reflexivity.
simpl. rewrite Int.add_zero; auto.
Qed.

Lemma mapsto_force_ptr: forall sh t v v', 
  mapsto sh t (force_ptr v) v' = mapsto sh t v v'.
Proof.
intros.
destruct v; simpl; auto.
Qed.

Hint Rewrite mapsto_force_ptr: norm.

Lemma mapsto_field_at:
  forall v1 v1' v2 sh ofs t structid fld fields,
   t = type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld ->
(*  access_mode t = By_value ch -> *)
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero v1' = offset_val (Int.repr ofs) v1 ->
  type_is_volatile t = false -> 
  mapsto sh t v1' v2 = field_at sh (Tstruct structid fields noattr) fld v2 v1.
Proof.
intros.
unfold field_at, mapsto.
rewrite tc_val_eq.
rewrite <- H.
rewrite field_offset_unroll.
rewrite H0.
normalize.
destruct (access_mode t); try rewrite andp_FF; auto.
rewrite <- H1.
rewrite offset_val_force_ptr.
destruct v1'; simpl; try rewrite andp_FF; auto.
Qed.

Lemma mapsto_field_at_:
  forall v1 v1' sh ofs t structid fld fields,
 (type_of_field
     (unroll_composite_fields structid (Tstruct structid fields noattr)
        fields) fld) = t ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero v1' = offset_val (Int.repr ofs) v1 ->
  (type_is_volatile
         (type_of_field
            (unroll_composite_fields structid
               (Tstruct structid fields noattr) fields) fld) = false) ->
  mapsto_ sh t v1'  = field_at_ sh (Tstruct structid fields noattr) fld v1.
Proof.
intros.
eapply mapsto_field_at; eauto.
rewrite H in H2; auto.
Qed.

(*
Lemma field_at_typecheck_val:
  forall t fld sh x y id fList att, 
     t = Tstruct id fList att ->
     field_at sh t fld x y = 
               !! (tc_val (type_of_field (unroll_composite_fields id t fList) fld) y) && field_at sh t fld x y.
Proof.
intros. subst.
unfold field_at.
apply pred_ext; normalize.
apply andp_right; [ | normalize].
unfold field_umapsto.
destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList)); normalize.
unfold umapsto.
destruct (access_mode
    (type_of_field (unroll_composite_fields id (Tstruct id fList att) fList) fld)); normalize.
destruct x; simpl; normalize.
apply orp_left; normalize.
Qed.
*)

Lemma field_at_isptr: forall t fld sh x y,
  field_at sh t fld y x = !!(isptr x) && field_at sh t fld y x.
Proof.
intros; apply pred_ext; normalize.
apply andp_right; auto.
unfold field_at.
destruct t; normalize.
destruct ( field_offset fld (unroll_composite_fields i (Tstruct i f a) f) ); normalize.
rewrite mapsto_isptr. apply andp_left1; auto.
destruct x; simpl; normalize.
Qed.

Lemma field_at_nonnull:  forall t fld sh x y, 
     field_at sh t fld y x = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_at sh t fld y x.
Proof.
intros; apply pred_ext; normalize.
apply andp_right; auto.
unfold field_at.
destruct t; normalize.
destruct ( field_offset fld (unroll_composite_fields i (Tstruct i f a) f) ); normalize.
rewrite mapsto_isptr. apply andp_left1; auto.
destruct x; simpl; normalize.
Qed.

Lemma field_at__nonnull:  forall t fld sh x, 
     field_at_ sh t fld x = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_at_ sh t fld x.
Proof.
intros.
apply field_at_nonnull.
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


Lemma field_umapsto_access_mode:
  forall sh v t fld v' id fList att,
   t = Tstruct id fList att ->
  field_at sh t fld v v' = 
   !! (exists ch, access_mode (type_of_field (unroll_composite_fields id t fList) fld) = By_value ch) 
           && field_at sh t fld v v'.
Proof.
intros. subst.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_at.
destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList)); normalize.
unfold mapsto.
case_eq (access_mode
    (type_of_field
       (unroll_composite_fields id (Tstruct id fList att) fList) fld)); intros; normalize.
apply prop_right; eauto.
Qed.

Lemma splice_top_top: Share.splice Tsh Tsh = Tsh.
Proof.
unfold Share.splice.
unfold Share.Lsh, Share.Rsh.
change Share.top with Tsh.
case_eq (Share.split Tsh); intros L R ?.
simpl.
do 2 rewrite Share.rel_top1.
erewrite Share.split_together; eauto.
Qed.

(*
Lemma field_at_offset:
  forall sh sid fields fld b i v ch,
  access_mode (type_of_field
        (unroll_composite_fields sid (Tstruct sid fields noattr) fields) fld) = By_value ch ->        
  field_at sh (Tstruct sid fields noattr) fld (Vptr b i) v |--
  match field_offset fld fields with
  | Errors.OK delta => 
     address_mapsto ch v (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh)
            (b, Int.unsigned (Int.add i (Int.repr delta)))
  | _ => FF
  end.
Proof.
unfold field_at; simpl; intros.
normalize.
destruct (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields noattr) fields)) 
  eqn:?.
2: rewrite field_offset_unroll in Heqr; rewrite Heqr; auto.
normalize.
rewrite field_offset_unroll in Heqr.
rewrite Heqr.
unfold mapsto. rewrite H.
apply orp_left; normalize.
Qed.
*)

Lemma mapsto_field_at':
  forall v1 v1' v2 sh ofs t structid fld fields,
  access_mode t = 
  access_mode (type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld) ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero v1' = offset_val (Int.repr ofs) v1 ->
  tc_val (type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld) v2  ->
  type_is_volatile (type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld) = false ->
  mapsto sh t v1' v2 |-- field_at sh (Tstruct structid fields noattr) fld v2 v1.
Proof.
intros.
rewrite offset_val_force_ptr in H1.
unfold field_at.
rewrite field_offset_unroll. rewrite H0.
rewrite H3.
unfold mapsto.
rewrite <- H.
case_eq (access_mode t); intros; try apply FF_left.
case_eq (type_is_volatile t); intros; try apply FF_left.
rewrite H3.
destruct v1'; normalize.
rewrite <- H1; simpl.
apply orp_left; normalize.
apply orp_right1; auto.
apply orp_right2; apply exp_right with v2'.
normalize.
Qed.

(*
Ltac mapsto_field_at_tac :=  
 eapply mapsto_field_at';
  [ simpl; reflexivity
  | unfold field_offset;  simpl; reflexivity
  | simpl; repeat rewrite Int.add_assoc; repeat f_equal; symmetry; apply Int.add_zero
  | simpl; reflexivity
  | simpl; reflexivity
  ].
*)

Lemma field_at_force_ptr: 
   forall sh t fld v2 v, field_at sh t fld v2 (force_ptr v) = field_at sh t fld v2 v.
Proof.
intros.
unfold field_at.
destruct t; normalize.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f)); normalize.
destruct v; simpl; reflexivity.
Qed.

Hint Rewrite field_at_force_ptr : norm.

Lemma field_at__isptr: forall t fld sh x,
  field_at_ sh t fld x = !!(isptr x) && field_at_ sh t fld x.
Proof.
intros.
apply field_at_isptr.
Qed.

Lemma field_at__force_ptr: forall t fld sh x,
  field_at_ sh t fld (force_ptr x) = field_at_ sh t fld x.
Proof.
intros.
unfold field_at_.
rewrite field_at_force_ptr. auto.
Qed.
Hint Rewrite field_at__force_ptr : norm.


Lemma field_at_nonvolatile:
  forall sh t fld v v', field_at sh t fld v' v = !!(type_is_volatile t = false) && field_at sh t fld v' v.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_at.
destruct t; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f)); try apply FF_left.
apply andp_left1.
apply prop_derives.
induction fld; simpl; auto.
Qed.

Lemma field_at__nonvolatile:
  forall sh t fld v, field_at_ sh t fld v = !!(type_is_volatile t = false) && field_at_ sh t fld v.
Proof.
 intros.
apply field_at_nonvolatile.
Qed.

Lemma address_mapsto_overlap:
  forall rsh sh ch1 v1 ch2 v2 a1 a2,
     adr_range a1 (Memdata.size_chunk ch1) a2 ->
     address_mapsto ch1 v1 rsh sh a1 * address_mapsto ch2 v2 rsh sh a2 |-- FF.
Proof.
 intros.
 apply res_predicates.address_mapsto_overlap.
 auto.
Qed.

Lemma mapsto_conflict:
 forall sh t v v2 v3,
 mapsto sh t v v2 * mapsto sh t v v3 |-- FF.
Proof.
intros.
unfold mapsto.
destruct (access_mode t); normalize.
destruct (type_is_volatile t); normalize.
pose proof (size_chunk_pos m).
destruct v; normalize.
rewrite distrib_orp_sepcon.
apply orp_left; normalize;
try (rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize;
      apply address_mapsto_overlap; split; auto; omega).
rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize; intros;
apply address_mapsto_overlap; split; auto; omega.
Qed.

Lemma field_at_conflict:
  forall sh t fld v v2 v3,
        field_at sh t fld v2 v
        * field_at sh t fld v3 v |-- FF.
Proof.
intros.
unfold field_at.
destruct t; try (rewrite FF_sepcon ; apply FF_left).
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f));
 try (rewrite FF_sepcon ; apply FF_left).
normalize.
apply mapsto_conflict.
Qed.

Lemma field_at__conflict:
  forall sh t fld v,
        field_at_ sh t fld v
        * field_at_ sh t fld v |-- FF.
Proof.
intros.
apply field_at_conflict.
Qed.

Lemma field_at_local_facts':
  forall sh t fld y x,
   field_at sh t fld y x |-- !!(isptr x).
Proof.
intros.
unfold field_at.
destruct t; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f));
  try apply FF_left.
rewrite mapsto_isptr.
normalize.
Qed.
Hint Resolve field_at_local_facts' : saturate_local.

Lemma field_at_local_facts:
 forall sh id t fList fld att (x y: val),
   t = Tstruct id fList att ->
   field_at sh t fld y x |--
      !! (isptr x  /\ type_is_volatile t = false).
Proof.
intros.
erewrite field_at_isptr.
rewrite field_at_nonvolatile.
normalize.
apply prop_right; repeat split; auto.
Qed.

Hint Extern 2 (@derives _ _ _ _) => 
   simple eapply field_at_local_facts; reflexivity : saturate_local.

Lemma field_at__local_facts:
 forall sh id t fList fld att (x: val),
   t = Tstruct id fList att ->
   field_at_ sh t fld x |--
      !! (isptr x /\ type_is_volatile t = false).
Proof.
intros.
eapply field_at_local_facts; eauto.
Qed.

Hint Extern 2 (@derives _ _ _ _) => 
   simple eapply field_at__local_facts; reflexivity : saturate_local.
