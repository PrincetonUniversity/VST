Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

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

(*
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
*)

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

Lemma lower_andp_val:
  forall (P Q: val->mpred) v, 
  ((P && Q) v) = (P v && Q v).
Proof. reflexivity. Qed.

Lemma mapsto_field_at:
  forall p p'  v' sh ofs t structid fld fields (v: reptype
    (nested_field_lemmas.nested_field_type2 (Tstruct structid fields noattr)
       (fld :: nil))),
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  type_is_volatile t = false -> 
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! (isSome (nested_field_rec (Tstruct structid fields noattr) (fld :: nil)))) 
  && mapsto sh t p' v' = field_at sh (Tstruct structid fields noattr) (fld :: nil) v p.
Proof.
  intros.
  rewrite field_at_data_at; [|exact H5].
  remember v as v''; assert (JMeq v'' v) by (subst v; reflexivity); clear Heqv''.
  revert v H6; 
  pattern (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) at 1 3.
  rewrite <- H0; intros.
  rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
  apply (field_offset_nested_field_offset2 structid fields noattr) in H1; subst ofs.
  rewrite <- H2.
  subst t; erewrite by_value_data_at; [|exact H| rewrite H4, H6; reflexivity].
  rewrite H2.
  apply pred_ext; normalize; repeat apply andp_right.
  + apply prop_right; split. 
    apply size_compatible_nested_field; tauto.
    apply align_compatible_nested_field; tauto.
  + rewrite <- H2. rewrite mapsto_offset_zero.
    cancel.
  + rewrite <- H2. rewrite mapsto_offset_zero.
    cancel.
Qed.

(* Original name is mapsto_field_at_, but I think current name is better. *)
Lemma mapsto__field_at_:
  forall p p' sh ofs t structid fld fields,
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  type_is_volatile t = false -> 
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! (isSome (nested_field_rec (Tstruct structid fields noattr) (fld :: nil)))) 
  && mapsto_ sh t p'  = field_at_ sh (Tstruct structid fields noattr) (fld::nil) p.
Proof.
  intros.
  eapply mapsto_field_at; eauto.
  rewrite <- H0; simpl.
  apply JMeq_sym, by_value_default_val, H.
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

(*
(* never used else where *)
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
*)

(*
(* never used elsewhere *)
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
*)

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

(*
Lemma by_value_access_mode_eq_type_eq: forall t t',
  type_is_by_value t ->
  access_mode t = access_mode t' ->
  t = t'.
Proof.
  intros.
  destruct t; [| destruct i, s, a| destruct s,a |destruct f | | | | | |];
  (destruct t'; [| destruct i, s, a| destruct s,a |destruct f | | | | | |]);
  simpl in *; inversion H0; try tauto.
*)

Lemma mapsto_field_at'':
  forall p p' v' sh ofs t structid fld fields (v: reptype (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil))),
  access_mode t = access_mode (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  tc_val (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) v' ->
  type_is_volatile (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) = false ->
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p /\  align_compatible (Tstruct structid fields noattr) p /\ isSome (nested_field_rec (Tstruct structid fields noattr) (fld :: nil)))) 
  && mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) (fld::nil) v p.
Proof.
  intros.
  rewrite field_at_data_at; [| exact H5].
  destruct (access_mode t) eqn:HH;
    try (unfold mapsto; rewrite HH; normalize; reflexivity).
  remember v' as v''; assert (JMeq v' v'') by (subst v'; reflexivity); clear Heqv''.
  assert (type_is_by_value t) by (destruct t; inversion HH; simpl; tauto).

  revert v' H6.
  pattern val at 1 2.
  erewrite <- by_value_reptype; [intros|exact H7].
  rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].  
  apply (field_offset_nested_field_offset2 structid fields noattr) in H0.
  subst ofs.
  rewrite <- H1; clear H1.
  (*erewrite by_value_data_at; [| exact H7|exact H6].*)
  admit.
Qed.

Lemma mapsto_field_at':
  forall p p' v' sh ofs t structid fld fields (v: reptype (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil))),
  access_mode t = access_mode (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) ->
  field_offset fld fields = Errors.OK ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  tc_val (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) v' ->
  type_is_volatile (nested_field_type2 (Tstruct structid fields noattr) (fld :: nil)) = false ->
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  size_compatible (Tstruct structid fields noattr) p ->
  align_compatible (Tstruct structid fields noattr) p ->
  isSome (nested_field_rec (Tstruct structid fields noattr) (fld :: nil)) -> 
  mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) (fld::nil) v p.
Proof.
  intros.
  eapply derives_trans; [ | eapply mapsto_field_at''; eassumption].
  normalize.
Qed.

(*
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
*)

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
(*
rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize; intros;
apply address_mapsto_overlap; split; auto; omega.
*)
(* originally, this proof is neccesary. but it is not now. I don't know why.  - Qinxiang *)
Qed.

Lemma memory_block_conflict: forall sh n m p,
  0 < n <= Int.max_unsigned -> 0 < m <= Int.max_unsigned ->
  memory_block sh (Int.repr n) p * memory_block sh (Int.repr m) p |-- FF.
Proof.
  intros.
  destruct H, H0.
Transparent memory_block.
  unfold memory_block.
Opaque memory_block.
  destruct p; normalize.
  remember (nat_of_Z (Int.unsigned (Int.repr n))) as n' eqn:Hn.
  rewrite Int.unsigned_repr in Hn; [| split; omega].
  rewrite <- (nat_of_Z_eq n) in H; [|omega].
  rewrite <- Hn in H.
  destruct n'; simpl in H; [omega|].

  remember (nat_of_Z (Int.unsigned (Int.repr m))) as m' eqn:Hm.
  rewrite Int.unsigned_repr in Hm; [| split; omega].
  rewrite <- (nat_of_Z_eq m) in H0; [|omega].
  rewrite <- Hm in H0.
  destruct m'; simpl in H0; [omega|].
  simpl.
  unfold mapsto_.
  apply derives_trans with (mapsto sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr (Int.unsigned i)))
     Vundef * mapsto sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr (Int.unsigned i)))
      Vundef * TT).
  cancel.
  apply derives_trans with (FF * TT).
  apply sepcon_derives; [|cancel].
  apply mapsto_conflict.
  normalize.
Qed.

(*
Lemma data_at'_conflict: forall sh e t pos v v' p,
  data_at' sh e t pos v p * data_at' sh e t pos v' p |-- FF.
Proof.
  intros.
  assert (32 < Int.max_unsigned).
    cbv.
    reflexivity.
  apply (type_mut
         (fun t => forall pos v v' p, data_at' sh e t pos v p * data_at' sh e t pos v' p |-- FF)
         (fun _ => True)
         (fun f => (forall alignment pos v v' p, sfieldlist_at' sh e f alignment pos v p *
         sfieldlist_at' sh e f alignment pos v' p |-- FF) /\ (forall size pos v v' p,
         ufieldlist_at' sh e f size pos v p * ufieldlist_at' sh e f size pos v' p |-- FF)));
    intros;
    simpl data_at'; simpl sfieldlist_at'; simpl ufieldlist_at';
    unfold at_offset2;
    try (repeat (rewrite at_offset'_eq; [|rewrite memory_block_offset_zero; reflexivity]);
    apply memory_block_conflict; split; omega);
    try (repeat (rewrite at_offset'_eq; [|rewrite mapsto_offset_zero; reflexivity]);
    apply mapsto_conflict).
Print sizeof.
*)

Lemma data_at_conflict: forall sh t v v' p,
  sizeof t > 0 ->
  legal_alignas_type t = true ->
  data_at sh t v p * data_at sh t v' p |-- FF.
Proof.
  intros.
  eapply derives_trans.
  + apply sepcon_derives.
    apply data_at_data_at_; assumption.
    apply data_at_data_at_; assumption.
  + destruct (nested_non_volatile_type t) eqn:HH.
    - rewrite <- memory_block_data_at_; try assumption.
      normalize.
      apply memory_block_conflict; admit. (* can be proved by size_compatible *)
    - unfold data_at_.
      eapply derives_trans; [apply sepcon_derives; apply data_at_non_volatile|].
      rewrite sepcon_prop_prop.
      rewrite HH.
      normalize.
      inversion H1.
Qed.

Lemma field_at_conflict: forall sh t fld p v v',
  sizeof (nested_field_type2 t (fld::nil)) > 0 ->
  legal_alignas_type t = true ->
  field_at sh t (fld::nil) v p * field_at sh t (fld::nil) v' p|-- FF.
Proof.
  intros.
  repeat (rewrite field_at_data_at; try assumption).
  repeat rewrite lower_andp_val.
  repeat (rewrite at_offset'_eq; [|rewrite <- data_at_offset_zero; reflexivity]).
  normalize.
  apply data_at_conflict; try assumption.
  apply nested_field_type2_nest_pred; [
    reflexivity| exact H0].
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  sizeof (nested_field_type2 t (fld::nil)) > 0 ->
  legal_alignas_type t = true ->
        field_at_ sh t (fld::nil) p
        * field_at_ sh t (fld::nil) p |-- FF.
Proof.
intros.
apply field_at_conflict; assumption.
Qed.