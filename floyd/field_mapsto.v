Require Import floyd.base.
Require Import floyd.assert_lemmas.

Local Open Scope logic.

Lemma tc_val_Vundef:
  forall t, ~ tc_val t Vundef.
Proof. destruct t; intro H; inv H.
Qed.

Lemma umapsto_tuint_tint:
  forall sh, umapsto sh tuint = umapsto sh tint.
Proof.
intros.
extensionality v1 v2.
reflexivity.
Qed.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh tuint = mapsto sh tint.
Proof.
intros.
unfold mapsto.
extensionality v1 v2.
reflexivity.
Qed.

Lemma mapsto_e:
 forall sh t v1 v2,
   mapsto sh t v1 v2 =
  match access_mode t with
  | By_value ch => 
    match v1 with
     | Vptr b ofs => 
         !!tc_val t v2 && address_mapsto ch v2 (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) (b, Int.unsigned ofs)
     | _ => FF
    end
  | _ => FF
  end. 
Proof.
unfold mapsto, umapsto; intros.
destruct (access_mode t) eqn:?; simpl;
 try solve [rewrite andp_comm; apply FF_andp];
destruct v1; simpl;  try solve [rewrite andp_comm; apply FF_andp].
apply pred_ext; normalize.
* apply orp_left. auto. normalize. contradiction (tc_val_Vundef _ H).
* apply orp_right1. auto.
Qed.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v, 
             mapsto sh tint v nullval = 
             mapsto sh (tptr t) v nullval.
Proof.
intros.
repeat rewrite mapsto_e.
simpl.
destruct v; auto. f_equal; auto.
f_equal.
apply prop_ext; split; intro; hnf in *|-*; auto.
Qed.

Lemma superprecise_mapsto:
  forall sh t v1 v2, predicates_sl.superprecise (mapsto sh t v1 v2).
Proof.
intros.
rewrite mapsto_e.
hnf; intros.
destruct (access_mode t); try contradiction.
destruct v1; try contradiction.
destruct H.
destruct H0.
eapply res_predicates.superprecise_address_mapsto; eauto.
intro; subst v2;  contradiction (tc_val_Vundef _ H).
Qed.

Lemma umapsto_isptr:
  forall sh t v1 v2,
   umapsto sh t v1 v2 = !! (isptr v1) && umapsto sh t v1 v2.
Proof.
intros; apply pred_ext; normalize.
apply andp_right; auto.
unfold umapsto.
destruct (access_mode t); normalize.
destruct v1; normalize.
apply prop_right; apply I.
Qed.


Lemma mapsto_isptr:
  forall sh t v1 v2,
   mapsto sh t v1 v2 = !! (isptr v1) && mapsto sh t v1 v2.
Proof.
intros. unfold mapsto. rewrite umapsto_isptr at 1.
apply pred_ext; normalize.
Qed.

Lemma mapsto__isptr:
  forall sh t v1,
   mapsto_ sh t v1 = !! (isptr v1) && mapsto_ sh t v1.
Proof.
intros.
unfold mapsto_. apply umapsto_isptr.
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

Definition field_umapsto (sh: Share.t) (t1: type) (fld: ident) (v2 v1: val) : mpred :=
 match t1 with
  |  Tstruct id fList  att =>
    let fList' := unroll_composite_fields id t1 fList in
    let t2 := type_of_field fList' fld in
     match field_offset fld fList' with
     | Errors.OK delta => 
            !!(type_is_volatile t2 = false) &&
               umapsto sh t2 (offset_val (Int.repr delta) v1) v2
     | _ => FF
     end
  | _  => FF
  end.

Definition field_mapsto sh t1 fld v1 v2 := !!(v2<>Vundef) && field_umapsto sh t1 fld v2 v1.
Definition field_mapsto_ sh t1 fld := field_umapsto sh t1 fld Vundef.
Arguments field_mapsto_ sh t1 fld v1 : simpl never.

Lemma field_mapsto_field_mapsto_:
  forall sh t1 fld v1 v2, field_mapsto sh t1 fld v1 v2 |-- field_mapsto_ sh t1 fld v1.
Proof.
intros.
unfold field_mapsto, field_mapsto_, field_umapsto.
normalize.
destruct t1; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f)); 
  try apply FF_left.
normalize.
unfold umapsto.
destruct (access_mode
    (type_of_field (unroll_composite_fields i (Tstruct i f a) f) fld)); auto.
destruct (offset_val (Int.repr z) v1); auto.
apply orp_left; normalize.
apply orp_right2.
apply exp_right with v2; normalize.
Qed.

Hint Resolve field_mapsto_field_mapsto_: cancel.

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

Lemma umapsto_force_ptr: forall sh t v v', 
  umapsto sh t (force_ptr v) v' = umapsto sh t v v'.
Proof.
intros.
destruct v; simpl; auto.
Qed.

Hint Rewrite umapsto_force_ptr mapsto_force_ptr: norm.

Lemma mapsto_field_mapsto_:
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
  mapsto_ sh t v1'  = field_mapsto_ sh (Tstruct structid fields noattr) fld v1.
Proof.
intros.
rewrite offset_val_force_ptr in H1.
unfold field_mapsto_, mapsto_.
unfold field_umapsto.
rewrite field_offset_unroll.
rewrite H0. rewrite H2. rewrite H.
rewrite <- H1.
normalize.
Qed.

Lemma field_mapsto_typecheck_val:
  forall t fld sh x y id fList att, 
     t = Tstruct id fList att ->
     field_mapsto sh t fld x y = 
               !! (tc_val (type_of_field (unroll_composite_fields id t fList) fld) y) && field_mapsto sh t fld x y.
Proof.
intros. subst.
unfold field_mapsto.
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

Lemma field_umapsto_isptr: forall t fld sh x y,
  field_umapsto sh t fld y x = !!(isptr x) && field_umapsto sh t fld y x.
Proof.
intros; apply pred_ext; normalize.
apply andp_right; auto.
unfold field_umapsto.
destruct t; normalize.
destruct ( field_offset fld (unroll_composite_fields i (Tstruct i f a) f) ); normalize.
rewrite umapsto_isptr. apply andp_left1; auto.
destruct x; simpl; normalize.
Qed.

Lemma field_mapsto_isptr: forall t fld sh x y,
  field_mapsto sh t fld x y = !!(isptr x) && field_mapsto sh t fld x y.
Proof.
intros.
unfold field_mapsto.
apply pred_ext; normalize.
rewrite field_umapsto_isptr; normalize.
Qed.

Lemma field_umapsto_nonnull:  forall t fld sh x y, 
     field_umapsto sh t fld y x = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_umapsto sh t fld y x.
Proof.
intros; apply pred_ext; normalize.
apply andp_right; auto.
unfold field_umapsto.
destruct t; normalize.
destruct ( field_offset fld (unroll_composite_fields i (Tstruct i f a) f) ); normalize.
rewrite umapsto_isptr. apply andp_left1; auto.
destruct x; simpl; normalize.
Qed.

Lemma field_mapsto__nonnull:  forall t fld sh x, 
     field_mapsto_ sh t fld x = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_mapsto_ sh t fld x.
Proof.
intros.
apply field_umapsto_nonnull.
Qed.

Lemma field_mapsto_nonnull:  forall t fld sh x y, 
     field_mapsto sh t fld x y = 
               !! (Cop.bool_val x (Tpointer t noattr) = Some true) && field_mapsto sh t fld x y.
Proof.
intros.
unfold field_mapsto.
rewrite field_umapsto_nonnull.
apply pred_ext; normalize.
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
  field_umapsto sh t fld v v' = 
   !! (exists ch, access_mode (type_of_field (unroll_composite_fields id t fList) fld) = By_value ch) 
           && field_umapsto sh t fld v v'.
Proof.
intros. subst.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_umapsto.
destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList)); normalize.
unfold umapsto.
case_eq (access_mode
    (type_of_field
       (unroll_composite_fields id (Tstruct id fList att) fList) fld)); intros; normalize.
apply prop_right; eauto.
Qed.

Lemma field_mapsto_access_mode:
  forall sh v t fld v' id fList att,
   t = Tstruct id fList att ->
  field_mapsto sh t fld v v' = 
   !! (exists ch, access_mode (type_of_field (unroll_composite_fields id t fList) fld) = By_value ch) 
           && field_mapsto sh t fld v v'.
Proof.
intros.
unfold field_mapsto.
rewrite (field_umapsto_access_mode _ _ _ _ _ _ _ _ H).
apply pred_ext; normalize.
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
unfold field_mapsto, field_umapsto; simpl; intros.
normalize.
destruct (field_offset fld
    (unroll_composite_fields sid (Tstruct sid fields noattr) fields)) 
  eqn:?.
2: rewrite field_offset_unroll in Heqr; rewrite Heqr; auto.
normalize.
rewrite field_offset_unroll in Heqr.
rewrite Heqr.
unfold umapsto. rewrite H.
apply orp_left; normalize.
Qed.

Lemma umapsto_field_umapsto:
  forall ch v1 v1' v2 sh ofs t structid fld fields,
   t = type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld ->
  access_mode t = By_value ch ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero v1' = offset_val (Int.repr ofs) v1 ->
  type_is_volatile t = false ->
  umapsto sh t v1' v2 = field_umapsto sh (Tstruct structid fields noattr) fld v2 v1.
Proof.
intros.
unfold field_umapsto, umapsto.
rewrite tc_val_eq.
rewrite <- H.
rewrite H0.
rewrite offset_val_force_ptr in H2.
rewrite field_offset_unroll.
rewrite H1. normalize. rewrite <- H2.
destruct v1'; simpl; auto.
Qed.

Lemma mapsto_field_mapsto:
  forall ch v1 v1' v2 sh ofs t structid fld fields,
   t = type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld ->
  access_mode t = By_value ch ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero v1' = offset_val (Int.repr ofs) v1 ->
  type_is_volatile t = false ->
  mapsto sh t v1' v2 = field_mapsto sh (Tstruct structid fields noattr) fld v1 v2.
Proof.
intros.
unfold field_mapsto, mapsto.
erewrite <- umapsto_field_umapsto by eassumption.
unfold umapsto.
rewrite H0.
destruct v1'; normalize.
apply pred_ext; normalize.
apply andp_right; auto.
apply prop_right; clear - H4; intro; subst.  contradiction (tc_val_Vundef _ H4).
apply orp_left; normalize. apply orp_right1; auto.
Qed.

Lemma umapsto_field_mapsto':
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
  umapsto sh t v1' v2 |-- field_mapsto sh (Tstruct structid fields noattr) fld v1 v2.
Proof.
intros.
rewrite offset_val_force_ptr in H1.
unfold field_mapsto, field_umapsto.
rewrite field_offset_unroll. rewrite H0.
rewrite H3.
unfold umapsto.
rewrite <- H.
case_eq (access_mode t); intros; try apply FF_left.
destruct v1'; normalize.
rewrite <- H1; simpl.
apply orp_left; normalize.
rewrite prop_true_andp. normalize.
apply orp_right1; auto.
clear - H5; intro; subst;  contradiction (tc_val_Vundef _ H5).
destruct (type_of_field
          (unroll_composite_fields structid (Tstruct structid fields noattr)
             fields) fld) ; contradiction.
Qed.

Ltac umapsto_field_mapsto_tac :=  
 eapply umapsto_field_mapsto';
  [ simpl; reflexivity
  | unfold field_offset;  simpl; reflexivity
  | simpl; repeat rewrite Int.add_assoc; repeat f_equal; symmetry; apply Int.add_zero
  | simpl; reflexivity
  | simpl; reflexivity
  ].

Lemma mapsto_field_mapsto':
  forall ch v1 v1' v2 sh ofs t structid fld fields,
  t = type_of_field
           (unroll_composite_fields structid (Tstruct structid fields noattr)
              fields) fld ->
  access_mode t = By_value ch ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero v1' = offset_val (Int.repr ofs) v1 ->
  tc_val t v2 ->
  type_is_volatile t = false ->
  mapsto sh t v1' v2 |-- field_mapsto sh (Tstruct structid fields noattr) fld v1 v2.
Proof.
intros.
erewrite mapsto_field_mapsto; eauto.
Qed.

Lemma field_umapsto_force_ptr: 
   forall sh t fld v2 v, field_umapsto sh t fld v2 (force_ptr v) = field_umapsto sh t fld v2 v.
Proof.
intros.
unfold field_umapsto.
destruct t; normalize.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f)); normalize.
destruct v; simpl; reflexivity.
Qed.

Lemma field_mapsto_force_ptr: 
   forall sh t fld v, field_mapsto sh t fld (force_ptr v) = field_mapsto sh t fld v.
Proof.
intros.
unfold field_mapsto.
extensionality y.
rewrite field_umapsto_force_ptr; auto.
Qed.
Hint Rewrite field_mapsto_force_ptr : norm.

Lemma field_mapsto_field_umapsto:
 forall sh t fld v v' id fList att,
  t = Tstruct id fList att ->
  field_mapsto sh t fld v v' =
  !! tc_val (type_of_field (unroll_composite_fields id t fList) fld) v' 
   && field_umapsto sh t fld v' v.
Proof.
intros.
unfold field_mapsto.
subst t.
unfold field_umapsto.
apply pred_ext; normalize.
* 
 destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList));
 normalize.
 apply andp_right; auto.
 unfold umapsto.
 destruct (access_mode
    (type_of_field (unroll_composite_fields id (Tstruct id fList att) fList)
       fld)); try apply FF_left.
 destruct (offset_val (Int.repr z) v); try apply FF_left.
 apply orp_left.
 apply andp_left1. apply prop_derives. intros; auto.
 normalize.
 apply andp_right; auto. apply prop_right; auto.
*
 destruct (field_offset fld (unroll_composite_fields id (Tstruct id fList att) fList));
   try apply FF_left.
 normalize.
 rewrite H0.
 apply andp_right; auto.
 apply prop_right. intro Hx; inv Hx. 
apply (tc_val_Vundef _ H).
 apply andp_right; auto. apply prop_right; auto.
Qed.

Lemma field_umapsto_field_mapsto:
  forall (sh : Share.t) (t : type) (id : ident) (v v' : val),
  v'<>Vundef ->
  field_umapsto sh t id v' v |-- field_mapsto sh t id v v'.
Proof.
intros.
unfold field_mapsto.
apply andp_right; auto.
apply prop_right; auto.
Qed.

Hint Extern 2 (field_umapsto _ _ _ _ _ |-- field_mapsto _ _ _ _ _) =>
    (apply field_umapsto_field_mapsto; congruence) : cancel.

Global Opaque field_mapsto.

Lemma field_mapsto__isptr: forall t fld sh x,
  field_mapsto_ sh t fld x = !!(isptr x) && field_mapsto_ sh t fld x.
Proof.
intros.
apply field_umapsto_isptr.
Qed.

Lemma field_mapsto__force_ptr: forall t fld sh x,
  field_mapsto_ sh t fld (force_ptr x) = field_mapsto_ sh t fld x.
Proof.
intros.
unfold field_mapsto_.
rewrite field_umapsto_force_ptr. auto.
Qed.
Hint Rewrite field_mapsto__force_ptr : norm.


Lemma field_umapsto_nonvolatile:
  forall sh t fld v v', field_umapsto sh t fld v' v = !!(type_is_volatile t = false) && field_umapsto sh t fld v' v.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
unfold field_umapsto.
destruct t; try apply FF_left.
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f)); try apply FF_left.
apply andp_left1.
apply prop_derives.
induction fld; simpl; auto.
Qed.

Lemma field_mapsto__nonvolatile:
  forall sh t fld v, field_mapsto_ sh t fld v = !!(type_is_volatile t = false) && field_mapsto_ sh t fld v.
Proof.
 intros.
apply field_umapsto_nonvolatile.
Qed.

Lemma field_mapsto_nonvolatile:
  forall sh t fld v v', field_mapsto sh t fld v v' = !!(type_is_volatile t = false) && field_mapsto sh t fld v v'.
Proof.
intros.
apply pred_ext; normalize.
apply andp_right; auto.
eapply derives_trans; [apply field_mapsto_field_mapsto_ | ].
rewrite field_mapsto__nonvolatile; normalize.
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

Lemma umapsto_conflict:
 forall sh t v v2 v3,
 umapsto sh t v v2 * umapsto sh t v v3 |-- FF.
Proof.
intros.
unfold umapsto.
destruct (access_mode t); normalize.
pose proof (size_chunk_pos m).
destruct v; normalize.
rewrite distrib_orp_sepcon.
apply orp_left; normalize;
try (rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize;
      apply address_mapsto_overlap; split; auto; omega).
rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize; intros;
apply address_mapsto_overlap; split; auto; omega.
Qed.

Lemma field_umapsto_conflict:
  forall sh t fld v v2 v3,
        field_umapsto sh t fld v2 v
        * field_umapsto sh t fld v3 v |-- FF.
Proof.
intros.
unfold field_umapsto.
destruct t; try (rewrite FF_sepcon ; apply FF_left).
destruct (field_offset fld (unroll_composite_fields i (Tstruct i f a) f));
 try (rewrite FF_sepcon ; apply FF_left).
normalize.
apply umapsto_conflict.
Qed.

Lemma field_mapsto__conflict:
  forall sh t fld v,
        field_mapsto_ sh t fld v
        * field_mapsto_ sh t fld v |-- FF.
Proof.
intros.
apply field_umapsto_conflict.
Qed.

Lemma field_mapsto_local_facts:
 forall sh id t fList fld att (x y: val),
   t = Tstruct id fList att ->
   field_mapsto sh t fld x y |--
      !! (isptr x /\ tc_val (type_of_field (unroll_composite_fields id t fList) fld) y
          /\ type_is_volatile t = false).
Proof.
intros.
erewrite field_mapsto_typecheck_val by eassumption.
erewrite field_mapsto_isptr.
rewrite field_mapsto_nonvolatile.
normalize.
apply prop_right; repeat split; auto.
Qed.

Hint Extern 2 (@derives _ _ _ _) => 
   simple eapply field_mapsto_local_facts; reflexivity : saturate_local.

Lemma field_mapsto__local_facts:
 forall sh id t fList fld att (x: val),
   t = Tstruct id fList att ->
   field_mapsto_ sh t fld x |--
      !! (isptr x /\ type_is_volatile t = false).
Proof.
intros.
rewrite field_mapsto__nonvolatile, field_mapsto__isptr.
normalize.
apply prop_right; split; auto.
Qed.

Hint Extern 2 (@derives _ _ _ _) => 
   simple eapply field_mapsto__local_facts; reflexivity : saturate_local.
