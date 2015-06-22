Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.type_induction.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.reptype_lemmas.
Require floyd.aggregate_pred. Import floyd.aggregate_pred.aggregate_pred.
Require Import floyd.data_at_lemmas.
Require Import floyd.jmeq_lemmas.

Local Open Scope logic.

(************************************************

Definition of nested_reptype_structlist, field_at, array_at, data_at, nested_sfieldlist_at

************************************************)

Section CENV.

Context {cs: compspecs}.
Context {csl: compspecs_legal cs}.

Definition field_at (sh: Share.t) (t: type) (gfs: list gfield) (v: reptype (nested_field_type2 t gfs)) (p: val): mpred :=
  (!! field_compatible t gfs p) && at_offset (data_at' sh (nested_field_type2 t gfs) v) (nested_field_offset2 t gfs) p.
Arguments field_at sh t gfs v p : simpl never.

Definition field_at_ (sh: Share.t) (t: type) (gfs: list gfield) : val -> mpred :=
  field_at sh t gfs (default_val (nested_field_type2 t gfs)).
Arguments field_at_ sh t gfs p : simpl never.

Definition data_at (sh: Share.t) (t: type) (v: reptype t) := field_at sh t nil v.

Definition data_at_ (sh: Share.t) (t: type) := field_at_ sh t nil.

Definition nested_reptype_structlist t gfs (m: members) := 
  compact_prod (map (fun it => reptype (nested_field_type2 t (StructField (fst it) :: gfs))) m).

Definition nested_reptype_unionlist t gfs (m: members) := 
  compact_sum (map (fun it => reptype (nested_field_type2 t (UnionField (fst it) :: gfs))) m).

Lemma nested_reptype_structlist_lemma: forall t gfs id a,
  nested_field_type2 t gfs = Tstruct id a ->
  reptype (nested_field_type2 t gfs) = nested_reptype_structlist t gfs (co_members (get_co id)).
Proof.
  intros.
  rewrite H, reptype_ind.
  unfold reptype_structlist, nested_reptype_structlist.
  f_equal.
  apply map_members_ext; [apply get_co_members_no_replicate |].
  intros.
  rewrite nested_field_type2_ind, H.
  simpl.
  auto.
Defined.

Lemma nested_reptype_unionlist_lemma: forall t gfs id a,
  nested_field_type2 t gfs = Tunion id a ->
  reptype (nested_field_type2 t gfs) = nested_reptype_unionlist t gfs (co_members (get_co id)).
Proof.
  intros.
  rewrite H, reptype_ind.
  unfold reptype_unionlist, nested_reptype_unionlist.
  f_equal.
  apply map_members_ext; [apply get_co_members_no_replicate |].
  intros.
  rewrite nested_field_type2_ind, H.
  simpl.
  auto.
Defined.

Definition nested_sfieldlist_at sh t gfs m (v: nested_reptype_structlist t gfs m) p: mpred :=
  match m with
  | nil => (!! field_compatible t gfs p) && emp
  | _ => struct_pred m (fun it v p =>
           withspacer sh
            (nested_field_offset2 t gfs +
              (field_offset cenv_cs (fst it) m + sizeof cenv_cs (field_type (fst it) m)))
            (nested_field_offset2 t gfs +
              field_offset_next cenv_cs (fst it) m (sizeof cenv_cs (nested_field_type2 t gfs)))
            (field_at sh t (StructField (fst it) :: gfs) v) p) v p
  end.

Definition nested_ufieldlist_at sh t gfs m (v: nested_reptype_unionlist t gfs m) (p: val): mpred :=
  match m with
  | nil => (!! field_compatible t gfs p) && emp
  | _ => union_pred m (fun it v p =>
           withspacer sh
            (nested_field_offset2 t gfs + sizeof cenv_cs (field_type (fst it) m))
            (nested_field_offset2 t gfs + sizeof cenv_cs (nested_field_type2 t gfs))
            (field_at sh t (UnionField (fst it) :: gfs) v) p) v p
  end.

Definition array_at (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z)
  (v: @zlist (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs))) (default_val _) (list_zlist _ _) lo hi) (p: val) : mpred :=
  (!! field_compatible0 t (ArraySubsc lo :: gfs) p) &&
  (!! field_compatible0 t (ArraySubsc hi :: gfs) p) &&
  array_pred lo hi
    (fun i v => at_offset (data_at' sh (nested_field_type2 t (ArraySubsc 0 :: gfs)) v)
       (nested_field_offset2 t (ArraySubsc i :: gfs))) v p.

Definition array_at_ (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z) :=
  array_at sh t gfs lo hi (zl_default _ _).  

(************************************************

field_compatible, local_facts, isptr and offset_zero properties

************************************************)

Lemma field_at_compatible:
  forall sh t path v c,
     field_at sh t path v c |-- !! field_compatible t path c.
Proof.
  intros.
  unfold field_at.
  normalize.
Qed.

Lemma field_at_compatible':
 forall sh t path v c,
     field_at sh t path v c =
     !! field_compatible t path c && field_at sh t path v c.
Proof.
intros.
apply pred_ext.
apply andp_right.
apply field_at_compatible.
auto.
normalize.
Qed.

Lemma field_at__compatible: forall sh t gfs p,
  field_at_ sh t gfs p |-- !! field_compatible t gfs p.
Proof.
  intros.
  unfold field_at_.
  apply field_at_compatible.
Qed.

Lemma data_at_compatible: forall sh t v p, data_at sh t v p |-- !! field_compatible t nil p.
Proof. intros. apply field_at_compatible. Qed.

Lemma data_at__compatible: forall sh t p, data_at_ sh t p |-- !! field_compatible t nil p.
Proof. intros.
 unfold data_at_. apply data_at_compatible.
Qed.

Lemma array_at_compatible: forall sh t gfs lo hi i v p,
  lo <= i <= hi ->
  array_at sh t gfs lo hi v p |-- !! field_compatible0 t (ArraySubsc i :: gfs) p.
Proof.
  intros.
  unfold array_at.
  apply andp_left1.
  rewrite !field_compatible0_cons.
  destruct (nested_field_type2 t gfs); try normalize.
  assert (0 <= i <= z) by omega.
  tauto.
Qed.

Lemma array_at__compatible: forall sh t gfs lo hi i p,
  lo <= i <= hi ->
  array_at_ sh t gfs lo hi p |-- !! field_compatible0 t (ArraySubsc i :: gfs) p.
Proof.
  intros.
  apply array_at_compatible; auto.
Qed.

(* called field_compatible0_array originally *)
Lemma array_at_compatible':
 forall i sh t gfs lo hi v p,
  (lo <= i <= hi)%Z ->
  array_at sh t gfs lo hi v p = !! field_compatible0 t (ArraySubsc i :: gfs) p && array_at sh t gfs lo hi v p.
Proof.
  intros.
  rewrite (add_andp _ _ (array_at_compatible sh t gfs lo hi i v p H)) at 1.
  normalize.
Qed.

Lemma field_at_local_facts: forall sh t gfs v p,
  field_at sh t gfs v p |-- !! isptr p.
Proof.
  intros.
  unfold field_at.
  apply andp_left1.
  apply prop_derives.
  apply field_compatible_isptr.
Qed.

Lemma field_at_isptr: forall sh t gfs v p,
  field_at sh t gfs v p = (!! isptr p) && field_at sh t gfs v p.
Proof. intros. apply local_facts_isptr. apply field_at_local_facts. Qed.

Lemma field_at_offset_zero: forall sh t gfs v p,
  field_at sh t gfs v p = field_at sh t gfs v (offset_val Int.zero p).
Proof. intros. apply local_facts_offset_zero.
 intros. rewrite field_at_isptr; normalize.
Qed.

Lemma field_at__local_facts: forall sh t gfs p,
  field_at_ sh t gfs p |-- !! isptr p.
Proof. intros. unfold field_at_. apply field_at_local_facts. Qed.

Lemma field_at__isptr: forall sh t gfs p,
  field_at_ sh t gfs p = (!! isptr p) && field_at_ sh t gfs p.
Proof. intros.
 unfold field_at_. apply field_at_isptr.
Qed.

Lemma field_at__offset_zero: forall sh t gfs p,
  field_at_ sh t gfs p = field_at_ sh t gfs (offset_val Int.zero p).
Proof. intros.
 unfold field_at_.
 apply field_at_offset_zero.
Qed.

Lemma data_at_local_facts: forall sh t v p, data_at sh t v p |-- !!(isptr p).
Proof. intros. unfold data_at. apply field_at_local_facts. Qed.
(*Hint Resolve data_at_local_facts : saturate_local.*)

Lemma data_at_isptr: forall sh t v p, data_at sh t v p = !!(isptr p) && data_at sh t v p.
Proof. intros. apply local_facts_isptr. apply data_at_local_facts. Qed.

Lemma data_at_offset_zero: forall sh t v p, data_at sh t v p = data_at sh t v (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity.
    intros; rewrite data_at_isptr; normalize.  
Qed.

Lemma data_at__local_facts: forall sh t p, data_at_ sh t p |-- !!(isptr p).
Proof. intros. unfold data_at_. apply data_at_local_facts. Qed.
(*Hint Resolve data_at__local_facts : saturate_local.*)

Lemma data_at__isptr: forall sh t p, data_at_ sh t p = !!(isptr p) && data_at_ sh t p.
Proof. intros. unfold data_at_. apply data_at_isptr. Qed.

Lemma data_at__offset_zero: forall sh t p, data_at_ sh t p = data_at_ sh t (offset_val Int.zero p).
Proof. intros. unfold data_at_. apply data_at_offset_zero. Qed.

(************************************************

Ext lemmas of array_at

************************************************)

Lemma array_at_ext_derives: forall sh t gfs lo hi v0 v1 p,
  (forall i u0 u1,
     lo <= i < hi ->
     JMeq u0 (zl_nth i v0) ->
     JMeq u1 (zl_nth i v1) ->
     field_at sh t (ArraySubsc i :: gfs) u0 p |--
     field_at sh t (ArraySubsc i :: gfs) u1 p) -> 
  array_at sh t gfs lo hi v0 p |-- array_at sh t gfs lo hi v1 p.
Proof.
  intros.
  unfold array_at.
  destruct (field_compatible0_dec t (ArraySubsc lo :: gfs) p);
    [| replace (!! field_compatible0 t (ArraySubsc lo :: gfs) p: mpred) with FF
         by (apply ND_prop_ext; tauto);
       normalize].
  destruct (field_compatible0_dec t (ArraySubsc hi :: gfs) p);
    [| replace (!! field_compatible0 t (ArraySubsc hi :: gfs) p: mpred) with FF
         by (apply ND_prop_ext; tauto);
       normalize].
  apply andp_derives; auto.
  apply array_pred_ext_derives.
  intros.
  generalize (H i).
  unfold field_at.
  replace (!! field_compatible t (ArraySubsc i :: gfs) p: mpred) with TT.
  Focus 2. {
    apply ND_prop_ext.
    rewrite field_compatible_cons.
    rewrite field_compatible0_cons in f, f0.
    destruct (nested_field_type2 t gfs); try tauto.
    assert (0 <= i < z) by omega.
    tauto.
  } Unfocus.
  erewrite nested_field_type2_ArraySubsc.
  intros.
  clear - H0 H1.
  specialize (H1 (zl_nth i v0) (zl_nth i v1) H0 JMeq_refl JMeq_refl).
  normalize in H1.
Qed.

Lemma array_at_ext: forall sh t gfs lo hi v0 v1 p,
  (forall i u0 u1,
     lo <= i < hi ->
     JMeq u0 (zl_nth i v0) ->
     JMeq u1 (zl_nth i v1) ->
     field_at sh t (ArraySubsc i :: gfs) u0 p =
     field_at sh t (ArraySubsc i :: gfs) u1 p) -> 
  array_at sh t gfs lo hi v0 p = array_at sh t gfs lo hi v1 p.
Proof.
  intros.
  apply pred_ext; apply array_at_ext_derives; intros.
  erewrite H by eauto; auto.
  erewrite <- H by eauto; auto.
Qed.

Lemma array_at_zl_equiv: forall sh t gfs lo hi v0 v1 p,
  zl_equiv v0 v1 ->
  array_at sh t gfs lo hi v0 p = array_at sh t gfs lo hi v1 p.
Proof.
  intros.
  apply array_at_ext.
  intros.
  rewrite H in H1 by auto.
  rewrite <- H2 in H1.
  rewrite H1.
  auto.
Qed.

(************************************************

Unfold and split lemmas

************************************************)

Lemma field_at_Tarray: forall sh t gfs t0 n a v1 v2 p,
  legal_nested_field t gfs ->
  nested_field_type2 t gfs = Tarray t0 n a ->
  0 <= n ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p = array_at sh t gfs 0 n v2 p.
Proof.
  intros.
  unfold field_at, array_at.
  unfold field_compatible0, field_compatible, legal_nested_field0.
  revert v1 v2 H2;
  rewrite (nested_field_type2_ind t (ArraySubsc 0 :: gfs)).
  rewrite H0; unfold gfield_type.
  intros.
  rewrite data_at'_ind.
  unfold legal_field0.
  rewrite at_offset_array_pred.
  f_equal.
  + assert (0 <= 0 <= n /\ 0 <= n <= n) by omega; normalize; apply ND_prop_ext; tauto.
  + apply array_pred_ext.
    intros.
    rewrite at_offset_eq.
    rewrite <- at_offset_eq2.
    rewrite !at_offset_eq.
    rewrite (nested_field_offset2_ind t (ArraySubsc i :: gfs))
      by (simpl; unfold legal_field; rewrite H0; auto).
    f_equal; [| rewrite H0; reflexivity].
    f_equal.
    unfold unfold_reptype.
    apply JMeq_eq.
    match goal with
    | |- JMeq (@eq_rect ?A ?x ?F ?v ?y ?H) _ =>
      rewrite (eq_rect_JMeq A x y F v H)
    end.
    auto.
Qed.

Lemma not_ptr_FF: forall A p, (A |-- !! isptr p) <-> (~ isptr p -> A = FF).
Proof.
  intros.
  split; intros.
  + apply pred_ext; [| apply FF_left].
    eapply derives_trans; [eauto |].
    apply prop_derives.
    auto.
  + destruct p; try solve [rewrite H by (simpl; congruence); apply FF_left].
    simpl.
    apply TT_right.
Qed.

Ltac solve_ptr_derives :=
  repeat rewrite isptr_offset_val;
  apply derives_refl.

Ltac solve_nptr p A :=
  let H := fresh "H" in
  match A with
  | (?B * ?C) % logic =>
     try solve [assert (~ isptr p -> B = FF) as H by solve_nptr p B;
                intro; rewrite H by auto ; apply FF_sepcon];
     try solve [assert (~ isptr p -> C = FF) as H by solve_nptr p C;
                intro; rewrite H by auto; apply sepcon_FF]
  | (?B && ?C) % logic =>
     try solve [assert (~ isptr p -> B = FF) as H by solve_nptr p B;
                intro; rewrite H by auto ; apply FF_andp];
     try solve [assert (~ isptr p -> C = FF) as H by solve_nptr p C;
                intro; rewrite H by auto; apply andp_FF]
  | _ => apply (proj1 (not_ptr_FF A p)); solve_ptr p A
  end
with solve_ptr p A :=
  let p0 := fresh "p" in
  match A with
  | (_ * _) % logic => apply (proj2 (not_ptr_FF A p)); solve_nptr p A
  | (_ && _) % logic => apply (proj2 (not_ptr_FF A p)); solve_nptr p A
  | (!! field_compatible _ _ ?q) => apply (derives_trans _ _ _ (prop_derives _ _ (field_compatible_isptr _ _ _))); solve_ptr_derives
  | (!! field_compatible0 _ _ ?q) => apply (derives_trans _ _ _ (prop_derives _ _ (field_compatible0_isptr _ _ _))); solve_ptr_derives
  | (memory_block _ _ ?q) => apply (derives_trans _ _ _ (memory_block_local_facts _ _ _)); solve_ptr_derives
  | (withspacer _ _ _ ?P p) => apply withspacer_preserve_local_facts;
                                     intro p0; solve_ptr p0 (P p0)
  | (at_offset ?P _ ?q) => apply (derives_trans _ (!! isptr q));
                           [apply at_offset_preserve_local_facts; intro p0; solve_ptr p0 (P p0) |
                            solve_ptr_derives]
  | (field_at _ _ _ _ p) => apply field_at_local_facts
  end.

Ltac destruct_ptr p :=
  let b := fresh "b" in
  let ofs := fresh "OFS" in
  match goal with
  | |- (@eq mpred) ?A ?B =>
       let H := fresh "H" in
       let H0 := fresh "H" in
       assert (~ isptr p -> A = FF) as H by solve_nptr p A;
       assert (~ isptr p -> B = FF) as H0 by solve_nptr p B;
       destruct p as [| | | | | b ofs]; try (rewrite H, H0 by (simpl; congruence); reflexivity);
       clear H H0;
       inv_int ofs
  | |- (?A |-- _) =>
       let H := fresh "H" in
       assert (~ isptr p -> A = FF) as H by solve_nptr p A;
       destruct p as [| | | | | b ofs]; try (rewrite H by (simpl; congruence); apply FF_left);
       clear H;
       inv_int ofs
  end.

(* Goal forall t gfs p, (!! field_compatible t gfs p) = (!! field_compatible0 t gfs p). *)
(*
Goal forall sh t gfs p, !! field_compatible t gfs (offset_val Int.zero Vundef) && at_offset (memory_block sh Int.zero) 14 (offset_val Int.zero p) = (!! field_compatible0 t gfs p).
intros.
destruct_ptr p.
*)

Lemma data_at_data_at': forall sh t v p,
  data_at sh t v p = !! field_compatible t nil p && data_at' sh t v p.
Proof.
  intros.
  unfold data_at, field_at.
  destruct_ptr p.
  destruct (field_compatible_dec t nil (Vptr b (Int.repr ofs))); [|
    replace (!!field_compatible t nil (Vptr b (Int.repr ofs)): mpred) with FF
      by (apply ND_prop_ext; tauto);
    normalize].
  f_equal.
  rewrite at_offset_eq3.
  rewrite nested_field_offset2_ind, Z.add_0_r by (unfold field_compatible in f; tauto).
  change (nested_field_type2 t nil) with t.
  auto.
Qed.

Lemma field_at_Tstruct: forall sh t gfs id a v1 v2 p,
  nested_field_type2 t gfs = Tstruct id a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p = nested_sfieldlist_at sh t gfs (co_members (get_co id)) v2 p.
Proof.
  intros.
  unfold field_at, nested_sfieldlist_at.
  revert v1 H0; rewrite H; intros.
  rewrite data_at'_ind.
  rewrite at_offset_struct_pred.
  rewrite andp_struct_pred by apply corable_prop.
  generalize (co_members (get_co id)) at 1 10; intro m; destruct m; [auto |].
  apply struct_pred_ext; [apply get_co_members_no_replicate |].
  
  intros.
  destruct_ptr p.
  unfold field_at, fst, snd.
  autorewrite with at_offset_db.
  unfold offset_val.
  solve_mod_modulus.
  normalize.
  destruct (legal_nested_field_dec t (StructField i :: gfs)).
  Focus 2. {
    replace (!!field_compatible t (StructField i :: gfs) (Vptr b (Int.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto; apply ND_prop_ext; tauto).
    simpl in n.
    rewrite H in n.
    simpl in n.
    replace (!!field_compatible t gfs (Vptr b (Int.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto; apply ND_prop_ext; tauto).
    normalize.
  } Unfocus.
  rewrite nested_field_offset2_ind with (gfs0 := StructField i :: gfs) by auto.
  unfold gfield_offset; rewrite H.
  f_equal; [| f_equal].
  + apply ND_prop_ext.
    rewrite field_compatible_cons, H.
    tauto.
  + rewrite sizeof_Tstruct.
    f_equal; [| f_equal; f_equal]; omega.
  + rewrite Z.add_assoc.
    erewrite data_at'_type_changable; [reflexivity | |].
    - simpl.
      rewrite nested_field_type2_ind.
      simpl; rewrite H.
      auto.
    - apply (proj_compact_prod_JMeq _ (i, field_type i _) (co_members (get_co id)) _ _ _ _ (unfold_reptype v1) v2); auto.
      * intros.
        rewrite nested_field_type2_ind, H.
        simpl.
        rewrite In_field_type; auto.
        apply get_co_members_no_replicate.
      * apply in_members_field_type; auto.
      * clear - H0.
        eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
Qed.

Lemma field_at_Tunion: forall sh t gfs id a v1 v2 p,
  nested_field_type2 t gfs = Tunion id a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p = nested_ufieldlist_at sh t gfs (co_members (get_co id)) v2 p.
Proof.
  intros.
  unfold field_at, nested_ufieldlist_at.
  revert v1 H0; rewrite H; intros.
  rewrite data_at'_ind.
  rewrite at_offset_union_pred.
  rewrite andp_union_pred by apply corable_prop.
  generalize (eq_refl (co_members (get_co id))).
  generalize (co_members (get_co id)) at 2 3 9; intro m; destruct m; [auto |].
  intro HH; assert (co_members (get_co id) <> nil) by congruence; clear HH.

  assert (
   forall i : ident,
   in_members i (co_members (get_co id)) ->
   reptype (snd (i, field_type i (co_members (get_co id)))) =
   reptype
     (nested_field_type2 t
        (UnionField (fst (i, field_type i (co_members (get_co id)))) :: gfs))).
  Focus 1. {
    clear - H.
    intros.
    unfold fst, snd.
    rewrite nested_field_type2_ind, H.
    reflexivity.
  } Unfocus.
  apply union_pred_ext; [apply get_co_members_no_replicate | |].
  Focus 1. {
    apply compact_sum_inj_JMeq; auto.
    + intros.
      rewrite nested_field_type2_ind, H.
      reflexivity.
    + eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
  } Unfocus.
  intros.
  destruct_ptr p.
  assert (in_members i (co_members (get_co id))).
  Focus 1. {
    change i with (fst (i, field_type i (co_members (get_co id)))).
    apply in_map with (f := fst).
    eapply compact_sum_inj_in; eauto.
  } Unfocus.
  unfold field_at, fst, snd.
  autorewrite with at_offset_db.
  unfold offset_val.
  solve_mod_modulus.
  normalize.
  destruct (legal_nested_field_dec t (UnionField i :: gfs)).
  Focus 2. {
    replace (!!field_compatible t (UnionField i :: gfs) (Vptr b (Int.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto).
    simpl in n.
    rewrite H in n.
    simpl in n.
    replace (!!field_compatible t gfs (Vptr b (Int.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto).
    normalize.
  } Unfocus.
  rewrite nested_field_offset2_ind with (gfs0 := UnionField i :: gfs) by auto.
  unfold gfield_offset; rewrite H.
  f_equal; [| f_equal].
  + apply ND_prop_ext.
    rewrite field_compatible_cons, H.
    tauto.
  + rewrite sizeof_Tunion.
    f_equal; [| f_equal; f_equal]; omega.
  + rewrite Z.add_0_r.
    erewrite data_at'_type_changable; [reflexivity | |].
    - simpl.
      rewrite nested_field_type2_ind.
      simpl; rewrite H.
      auto.
    - unfold proj_union.
      apply (proj_compact_sum_JMeq _ (i, field_type i (co_members (get_co id))) (co_members (get_co id)) _ _ d0 d1 (unfold_reptype v1) v2); auto.
      * intros (i0, t0) ?.
        rewrite nested_field_type2_ind, H.
        simpl.
        auto.
      * eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
Qed.

Lemma array_at_len_0: forall sh t gfs i v p,
  array_at sh t gfs i i v p = !! field_compatible0 t (ArraySubsc i :: gfs) p && emp.
Proof.
  intros.
  unfold array_at.
  rewrite array_pred_len_0 by omega.
  f_equal.
  apply andp_dup.
Qed.

Lemma array_at_len_1: forall sh t gfs i v v0 p,
  JMeq (zl_nth i v) v0 ->
  array_at sh t gfs i (i + 1) v p = field_at sh t (ArraySubsc i :: gfs) v0 p.
Proof.
  intros.
  unfold array_at, field_at.
  rewrite array_pred_len_1.
  rewrite !at_offset_eq.
  f_equal.
  + rewrite (ND_prop_ext _ _ (field_compatible_field_compatible0' t i gfs p)).
    normalize.
  + erewrite data_at'_type_changable; [reflexivity | | auto].
    - rewrite !nested_field_type2_ind with (gfs0 := _ :: gfs).
      destruct (nested_field_type2 t gfs); auto.
Qed.

Lemma split2_array_at: forall sh t gfs lo mid hi v p,
  lo <= mid <= hi ->
  array_at sh t gfs lo hi v p =
  array_at sh t gfs lo mid (zl_sublist lo mid v) p * 
  array_at sh t gfs mid hi (zl_sublist mid hi v) p.
Proof.
  intros.
  unfold array_at.
  revert v; rewrite nested_field_type2_ind; intros.
  rewrite !field_compatible0_cons with (gfs0 := gfs).
  destruct (nested_field_type2 t gfs); try solve [change (!! False: mpred) with FF; normalize].
  rewrite split_array_pred with (mid0 := mid) by auto.
  normalize.
  f_equal.
  apply ND_prop_ext.
  assert (0 <= lo -> 0 <= mid) by omega.
  assert (hi <= z -> mid <= z) by omega.
  tauto.
Qed.

Existing Instance list_zlist_correct.

Lemma split3seg_array_at: forall sh t gfs lo ml mr hi v p,
  lo <= ml ->
  ml <= mr ->
  mr <= hi ->
  array_at sh t gfs lo hi v p =
    array_at sh t gfs lo ml (zl_sublist lo ml v) p*
    array_at sh t gfs ml mr (zl_sublist ml mr v) p*
    array_at sh t gfs mr hi (zl_sublist mr hi v) p.
Proof.
  intros.
  rewrite split2_array_at with (lo := lo) (mid := ml) (hi := hi) by omega.
  rewrite split2_array_at with (lo := ml) (mid := mr) (hi := hi) by omega.
  rewrite sepcon_assoc.
  f_equal.
  f_equal.
  + apply array_at_zl_equiv.
    apply zl_sub_sub; omega.
  + apply array_at_zl_equiv.
    apply zl_sub_sub; omega.
Qed.

Lemma split3_array_at: forall sh t gfs lo mid hi v v0 p,
  lo <= mid < hi ->
  JMeq v0 (zl_nth mid v) ->
  array_at sh t gfs lo hi v p =
    array_at sh t gfs lo mid (zl_sublist lo mid v) p *
    field_at sh t (ArraySubsc mid :: gfs) v0 p *
    array_at sh t gfs (mid + 1) hi (zl_sublist (mid + 1) hi v) p.
Proof.
  intros.
  rewrite split3seg_array_at with (ml := mid) (mr := mid + 1) by omega.
  f_equal.
  f_equal.
  apply array_at_len_1.
  rewrite zl_sublist_correct by omega.
  symmetry; auto.
Qed.

(*
Lemma data_at_field_at: forall sh t, data_at sh t = field_at sh t nil.
Proof. intros. reflexivity. Qed.

Lemma data_at__field_at_: forall sh t, data_at_ sh t = field_at_ sh t nil.
Proof. intros. reflexivity. Qed.

Lemma data_at_field_at_cancel:
  forall sh t v p, data_at sh t v p |-- field_at sh t nil v p.
Proof. intros; rewrite data_at_field_at; auto. Qed.

Lemma field_at_data_at_cancel:
  forall sh t v p, field_at sh t nil v p |-- data_at sh t v p.
Proof. intros; rewrite data_at_field_at; auto. Qed.

Hint Extern 1 (data_at _ _ _ _ |-- field_at _ _ nil _ _) =>
    (apply data_at_field_at_cancel) : cancel.

Hint Extern 1 (field_at _ _ nil _ _ |-- data_at _ _ _ _) =>
    (apply field_at_data_at_cancel) : cancel.
(* dont think we need it any more. If we need, just do unfold in Hint database instead. *)  
*)

(************************************************

Reroot lemmas

************************************************)

Lemma field_at_data_at: forall sh t gfs v p,
  field_at sh t gfs v p =
  data_at sh (nested_field_type2 t gfs) v (field_address t gfs p).
Proof.
  intros.
  unfold data_at, field_at.
  unfold field_address.
  if_tac.
  + rewrite <- at_offset_eq.
    destruct_ptr p.
    autorewrite with at_offset_db.
    rewrite (nested_field_offset2_ind (nested_field_type2 t gfs) nil) by (simpl; tauto).
    rewrite Z.add_0_r.
    generalize (field_compatible_nested_field t gfs (Vptr b (Int.repr ofs)));
    unfold offset_val in *;
    solve_mod_modulus;
    intros.
    f_equal. (* It magically solved the potential second subgoal *)
    apply ND_prop_ext.
    tauto.
  + replace (!!field_compatible (nested_field_type2 t gfs) nil Vundef: mpred) with FF
      by (apply ND_prop_ext; unfold field_compatible; simpl isptr; tauto).
    replace (!!field_compatible t gfs p : mpred) with FF
      by (apply ND_prop_ext; tauto).
    normalize.
Qed.

Lemma field_at__data_at_: forall sh t gfs p,
  field_at_ sh t gfs p = 
  data_at_ sh (nested_field_type2 t gfs) (field_address t gfs p).
Proof.
  intros.
  unfold field_at_, data_at_.
  apply field_at_data_at.
Qed.

Lemma lifted_field_at_data_at: forall sh t gfs v p,
  `(field_at sh t gfs) v p =
  `(data_at sh (nested_field_type2 t gfs)) v (`(field_address t gfs) p).
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at_data_at.
Qed.

Lemma lifted_field_at__data_at_: forall sh t gfs p,
  `(field_at_ sh t gfs) p =
  `(data_at_ sh (nested_field_type2 t gfs)) (`(field_address t gfs) p).
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at__data_at_.
Qed.

Lemma array_at_data_at: forall sh t gfs lo hi v p,
  array_at sh t gfs lo hi v p =
  (!! field_compatible0 t (ArraySubsc lo :: gfs) p) &&
  (!! field_compatible0 t (ArraySubsc hi :: gfs) p) &&
  at_offset (data_at sh (nested_field_array_type t gfs lo hi) (@fold_reptype _ _ (nested_field_array_type t gfs lo hi)  (zl_shift 0 (hi - lo) v))) (nested_field_offset2 t (ArraySubsc lo :: gfs)) p.
Proof.
  intros.
  unfold array_at.
  rewrite at_offset_eq.
  rewrite data_at_data_at'.
  unfold nested_field_array_type at 2.
  rewrite data_at'_ind.
  rewrite <- at_offset_eq.
  rewrite at_offset_array_pred.
  destruct (field_compatible0_dec t (ArraySubsc lo :: gfs) p); [|
    replace (!! field_compatible0 t (ArraySubsc lo :: gfs) p: mpred) with FF
      by (apply ND_prop_ext; tauto);
    normalize].
  destruct (field_compatible0_dec t (ArraySubsc hi :: gfs) p); [|
    replace (!! field_compatible0 t (ArraySubsc hi :: gfs) p: mpred) with FF
      by (apply ND_prop_ext; tauto);
    normalize].
  pose proof field_compatible0_nested_field_array t gfs lo hi p f f0.
  normalize.

  rewrite unfold_fold_reptype.
  symmetry; apply array_pred_shift with (mv := lo); [omega | omega |].
  intros.
  rewrite !at_offset_eq.
  rewrite offset_offset_val.
  rewrite add_repr.
  f_equal.
  f_equal.
  f_equal.
  assert (field_compatible0 t (ArraySubsc i :: gfs) p).
  Focus 1. {
    unfold field_compatible0 in *.
    simpl in f, f0 |- *.
    destruct (nested_field_type2 t gfs); try tauto.
    simpl in f, f0 |- *.
    assert (0 <= i <= z) by omega.
    tauto.
  } Unfocus.
  unfold field_compatible0 in *.
  rewrite nested_field_type2_ind.
  rewrite !nested_field0_offset2_ind with (gfs0 := _ :: gfs) by tauto.
  simpl in f.
  destruct (nested_field_type2 t gfs); try tauto.
  simpl.
  pose_size_mult cenv_cs t0 (i - i' :: lo :: i - i' :: nil).
  omega.
Qed.

Lemma array_at_data_at_with_tl: forall sh t gfs lo mid hi v v' p,
  array_at sh t gfs lo mid v p * array_at sh t gfs mid hi v' p =
  data_at sh (nested_field_array_type t gfs lo mid) (@fold_reptype _ _ (nested_field_array_type t gfs lo mid)  (zl_shift 0 (mid - lo) v)) (field_address0 t (ArraySubsc lo :: gfs) p) *
  array_at sh t gfs mid hi v' p.
Proof.
  intros.
  rewrite (array_at_data_at sh t gfs lo mid).
  rewrite at_offset_eq.
  unfold field_address0.
  destruct (field_compatible0_dec t (ArraySubsc lo :: gfs) p).
  + unfold array_at; normalize.
    f_equal.
    apply ND_prop_ext; tauto.
  + replace (!! field_compatible0 t (ArraySubsc lo :: gfs) p: mpred) with FF
      by (apply ND_prop_ext; tauto).
    rewrite data_at_isptr with (p := Vundef).
    change (!!isptr Vundef: mpred) with FF.
    normalize.
Qed.

(************************************************

Lemmas about underscore and memory_block

************************************************)

Lemma field_at_field_at_: forall sh t gfs v p, 
  field_at sh t gfs v p |-- field_at_ sh t gfs p.
Proof.
  intros.
  destruct (field_compatible_dec t gfs p).
  + destruct_ptr p.
    unfold field_at_, field_at.
    apply andp_derives; auto.
    pose proof field_compatible_nested_field _ _ _ f.
    unfold field_compatible in H, f.
    unfold offset_val in H.
    autorewrite with at_offset_db in *.
    destruct (zlt 0 (sizeof cenv_cs (nested_field_type2 t gfs))).
    - unfold align_compatible, size_compatible in *.
      revert H f; solve_mod_modulus; intros.
      pose proof nested_field_offset2_in_range t gfs.
      spec H1; [tauto |].
      spec H1; [tauto |].
      rewrite (Z.mod_small ofs) in * by omega.
      rewrite (Z.mod_small (ofs + nested_field_offset2 t gfs) Int.modulus) in H by omega.
      apply data_at'_data_at'_; try tauto; omega.
    - assert (sizeof cenv_cs (nested_field_type2 t gfs) = 0)
        by (pose proof sizeof_pos cenv_cs (nested_field_type2 t gfs); omega).
      rewrite !empty_data_at' by tauto.
      auto.
  + unfold field_at_, field_at.
    normalize.
Qed.

Lemma field_at__memory_block: forall sh t gfs p, 
  field_at_ sh t gfs p =
  memory_block sh (sizeof cenv_cs (nested_field_type2 t gfs)) (field_address t gfs p).
Proof.
  intros.
  unfold field_address.
  destruct (field_compatible_dec t gfs p).
  + unfold field_at_, field_at.
    destruct_ptr p.
    autorewrite with at_offset_db in *.
    unfold offset_val.
    solve_mod_modulus.
    pose proof field_compatible_nested_field _ _ _ f.
    revert H f;
    unfold field_compatible;
    unfold size_compatible, align_compatible, offset_val;
    solve_mod_modulus;
    intros.
    destruct (zlt 0 (sizeof cenv_cs (nested_field_type2 t gfs))).
    - pose proof nested_field_offset2_in_range t gfs.
      spec H1; [tauto |].
      spec H1; [tauto |].
      rewrite (Z.mod_small ofs) in * by omega.
      rewrite (Z.mod_small (ofs + nested_field_offset2 t gfs) Int.modulus) in H by omega.
      rewrite memory_block_data_at'_default_val by (try tauto; omega).
      normalize.
    - assert (sizeof cenv_cs (nested_field_type2 t gfs) = 0)
        by (pose proof sizeof_pos cenv_cs (nested_field_type2 t gfs); omega).
      rewrite !empty_data_at' by tauto.
      rewrite H1, memory_block_zero.
      normalize.
  + unfold field_at_, field_at.
    rewrite memory_block_isptr.
    replace (!!field_compatible t gfs p : mpred) with FF by (apply ND_prop_ext; tauto).
    replace (!!isptr Vundef : mpred) with FF by reflexivity.
    normalize.
Qed.

Lemma data_at_data_at_ : forall sh t v p, 
  data_at sh t v p |-- data_at_ sh t p.
Proof.
  intros.
  apply field_at_field_at_.
Qed.

Lemma data_at__memory_block: forall sh t p,
  data_at_ sh t p =
  (!! field_compatible t nil p) && memory_block sh (sizeof cenv_cs t) p.
Proof.
  intros.
  unfold data_at_, data_at.
  rewrite field_at__memory_block.
  unfold field_address.
  if_tac.
  + normalize.
  + unfold field_at_, field_at.
    rewrite memory_block_isptr.
    replace (!!field_compatible t nil p : mpred) with FF by (apply ND_prop_ext; tauto).
    replace (!!isptr Vundef : mpred) with FF by reflexivity.
    normalize.
Qed.

Lemma memory_block_data_at_: forall sh t p,
  field_compatible t nil p ->
  memory_block sh (sizeof cenv_cs t) p = data_at_ sh t p.
Proof.
  intros.
  rewrite data_at__memory_block.
  normalize.
Qed.

Lemma data_at__memory_block_cancel:
   forall sh t p, 
       data_at_ sh t p |-- memory_block sh (sizeof cenv_cs t) p.
Proof.
  intros.
  rewrite data_at__memory_block.
  normalize.
Qed.

Lemma data_at_memory_block:
  forall sh t v p, 
     data_at sh t v p |-- memory_block sh (sizeof cenv_cs t) p.
Proof.
  intros.
  eapply derives_trans; [apply data_at_data_at_; reflexivity |].
  rewrite data_at__memory_block.
  apply andp_left2.
  auto.
Qed.

(*
(* originaly, premises are nested_non_volatile, sizeof < modulus, sizeof = sz *)
Hint Extern 1 (data_at_ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at__memory_block_cancel;
       [reflexivity 
       | rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l;simpl; 
         repable_signed 
       | try apply f_equal_Int_repr;
         rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l; simpl; repable_signed
       ])
    : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at_memory_block; 
       [reflexivity 
       | rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l;simpl; 
         repable_signed 
       | try apply f_equal_Int_repr;
         rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l; simpl; repable_signed
       ])
    : cancel.
*)

Lemma array_at_array_at_: forall sh t gfs lo hi v p, 
  array_at sh t gfs lo hi v p |-- array_at_ sh t gfs lo hi p.
Proof.
  intros.
  apply array_at_ext_derives.
  intros.
  destruct (field_compatible0_dec t (ArraySubsc i :: gfs) p).
  + rewrite zl_default_correct in H1 by auto.
    revert u1 H1; erewrite <- nested_field_type2_ArraySubsc with (i0 := i); intros.
    rewrite H1.
    apply field_at_field_at_.
  + unfold field_at.
    replace (!! field_compatible t (ArraySubsc i :: gfs) p : mpred) with FF; [normalize |].
    pose proof field_compatible_field_compatible0 t (ArraySubsc i :: gfs) p.
    apply ND_prop_ext; tauto.
Qed.

(************************************************

Other lemmas

************************************************)

Lemma lower_andp_val:
  forall (P Q: val->mpred) v, 
  ((P && Q) v) = (P v && Q v).
Proof. reflexivity. Qed.

Lemma compute_legal_nested_field_spec: forall {A : Type} {ND : NatDed A} (P: A) t gfs,
  Forall (fun Q => P |-- !!Q) (compute_legal_nested_field t gfs) ->
  P |-- !! (legal_nested_field t gfs).
Proof.
  intros.
  induction gfs as [| gf gfs].
  + simpl.
    apply prop_right; auto.
  + simpl in H |- *.
    unfold legal_field.
    destruct (nested_field_type2 t gfs), gf; inversion H; subst;
    try
    match goal with
    | HH : P |-- (prop False) |-
           P |-- (prop (_)) => apply (derives_trans _ _ _ HH); apply prop_derives; tauto
    end.
    - apply IHgfs in H3.
      rewrite (add_andp _ _ H2).
      rewrite (add_andp _ _ H3).
      normalize.
      apply prop_right; tauto.
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H. 
        apply (derives_trans _ _ _ H), prop_derives; tauto.
      * inversion H1.
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H. 
        apply (derives_trans _ _ _ H), prop_derives; tauto.
      * inversion H.
        apply (derives_trans _ _ _ H6), prop_derives; tauto.
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H. 
        apply (derives_trans _ _ _ H), prop_derives; tauto.
      * inversion H1.
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H. 
        apply (derives_trans _ _ _ H), prop_derives; tauto.
      * inversion H.
        apply (derives_trans _ _ _ H6), prop_derives; tauto.
Qed.

(*
Lemma field_at_field_at: forall sh t gfs0 gfs1 v v' p,
  legal_alignas_type t = true ->
  JMeq v v' ->
  field_at sh t (gfs1 ++ gfs0) v p =
  (!! (size_compatible t p)) &&
  (!! (align_compatible t p)) &&
  (!! (legal_nested_field t (gfs1 ++ gfs0))) &&
  at_offset' (field_at sh (nested_field_type2 t gfs0) gfs1 v') (nested_field_offset2 t gfs0) p.
Proof.
  intros.
  rewrite at_offset'_eq; [| rewrite <- field_at_offset_zero; reflexivity].
  unfold field_at.
  simpl.
  revert v' H0.
  rewrite nested_field_type2_nested_field_type2.
  intros.
  rewrite <- H0.
  clear H0 v'.
  rewrite data_at'_at_offset'; 
   [ rewrite at_offset'_eq; [| rewrite <- data_at'_offset_zero; reflexivity]
   | apply nested_field_type2_nest_pred; simpl; auto
   | apply nested_field_offset2_type2_divide; auto].
  rewrite data_at'_at_offset' with (pos := (nested_field_offset2 (nested_field_type2 t gfs0) gfs1)); 
   [ rewrite at_offset'_eq; [| rewrite <- data_at'_offset_zero; reflexivity]
   | apply nested_field_type2_nest_pred; simpl; auto
   | rewrite <- nested_field_type2_nested_field_type2;
     apply nested_field_offset2_type2_divide; apply nested_field_type2_nest_pred; simpl; auto].
  apply pred_ext; normalize; rewrite <- nested_field_offset2_app; normalize.
  apply andp_right; [apply prop_right | apply derives_refl].
  split; [| split; split]; auto.
  + apply size_compatible_nested_field, H0.
    eapply legal_nested_field_app, H2.
  + apply align_compatible_nested_field, H1; auto.
    eapply legal_nested_field_app, H2.
  + apply legal_nested_field_app', H2.
Qed.
*)

(*
Lemma mapsto_field_at:
  forall p p'  v' sh t structid fld fields (v: reptype
    (nested_field_lemmas.nested_field_type2 (Tstruct structid fields noattr)
       fld)),
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  p' = (field_address (Tstruct structid fields noattr) fld p) ->
  type_is_volatile t = false -> 
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! (legal_nested_field (Tstruct structid fields noattr) fld))
  && mapsto sh t p' v' = field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  rewrite field_at_data_at.
  remember v as v''; assert (JMeq v'' v) by (subst v; reflexivity); clear Heqv''.
  revert v H5; 
  pattern (nested_field_type2 (Tstruct structid fields noattr) fld) at 1 3.
  rewrite <- H0; intros.
  rewrite <- H1.
  subst t; erewrite by_value_data_at; [|exact H| rewrite H3, H5; reflexivity].
  rewrite H1.
  apply pred_ext; normalize; repeat apply andp_right.
  + apply prop_right; split; [| split].
    - unfold field_address.
      if_tac; [| simpl; auto].
      apply size_compatible_nested_field; tauto.
    - unfold field_address.
      if_tac; [| simpl; auto].
      apply align_compatible_nested_field; tauto.
    - apply (nested_field_type2_nest_pred); eauto.
  + rewrite <- H1. apply derives_refl.
  + unfold field_address.
    if_tac; [| rewrite mapsto_isptr; simpl; normalize].
    unfold field_compatible in H8; destruct H8 as [? [? [? [? ?]]]].
    normalize.
  + rewrite <- H1. apply derives_refl.
Qed.

Lemma mapsto__field_at_:
  forall p p' sh t structid fld fields,
  type_is_by_value t ->
  t = (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  p' = (field_address (Tstruct structid fields noattr) fld p) ->
  type_is_volatile t = false -> 
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p)) && (!! (align_compatible (Tstruct structid fields noattr) p)) && (!! legal_nested_field (Tstruct structid fields noattr) fld)
  && mapsto_ sh t p'  = field_at_ sh (Tstruct structid fields noattr) fld p.
Proof.
  intros.
  eapply mapsto_field_at; eauto.
  rewrite <- H0; simpl.
  apply JMeq_sym, by_value_default_val, H.
Qed.

(*
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
  forall p p' v' sh ofs t structid fld fields (v: reptype (nested_field_type2 (Tstruct structid fields noattr) fld)),
  access_mode t = access_mode (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  nested_field_offset2 (Tstruct structid fields noattr) fld = ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  tc_val (nested_field_type2 (Tstruct structid fields noattr) fld) v' ->
  type_is_volatile (nested_field_type2 (Tstruct structid fields noattr) fld) = false ->
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  (!! (size_compatible (Tstruct structid fields noattr) p /\  align_compatible (Tstruct structid fields noattr) p /\ legal_nested_field (Tstruct structid fields noattr) fld)) 
  && mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  rewrite field_at_data_at.
  destruct (access_mode t) eqn:HH;
    try (unfold mapsto; rewrite HH; normalize; reflexivity).
  remember v' as v''; assert (JMeq v' v'') by (subst v'; reflexivity); clear Heqv''.
  assert (type_is_by_value t) by (destruct t; inversion HH; simpl; tauto).

  revert v' H6.
  pattern val at 1 2.
  erewrite <- by_value_reptype; [intros|exact H7].
  subst ofs.
(* rewrite <- H1; clear H1. *)
(*  erewrite by_value_data_at; [| exact H7|exact H6]. *)
  admit.
Qed.

Lemma mapsto_field_at':
  forall p p' v' sh ofs t structid fld fields (v: reptype (nested_field_type2 (Tstruct structid fields noattr) fld)),
  access_mode t = access_mode (nested_field_type2 (Tstruct structid fields noattr) fld) ->
  nested_field_offset2 (Tstruct structid fields noattr) fld = ofs ->
  offset_val Int.zero p' = offset_val (Int.repr ofs) p ->
  tc_val (nested_field_type2 (Tstruct structid fields noattr) fld) v' ->
  type_is_volatile (nested_field_type2 (Tstruct structid fields noattr) fld) = false ->
  JMeq v' v ->
  legal_alignas_type (Tstruct structid fields noattr) = true ->
  size_compatible (Tstruct structid fields noattr) p ->
  align_compatible (Tstruct structid fields noattr) p ->
  legal_nested_field (Tstruct structid fields noattr) fld -> 
  mapsto sh t p' v' |-- field_at sh (Tstruct structid fields noattr) fld v p.
Proof.
  intros.
  eapply derives_trans; [ | eapply mapsto_field_at''; eassumption].
  normalize.
Qed.
*)
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
      apply res_predicates.address_mapsto_overlap; split; auto; omega).
(*
rewrite sepcon_comm; rewrite distrib_orp_sepcon; apply orp_left; normalize; intros;
apply address_mapsto_overlap; split; auto; omega.
*)
(* originally, this proof is neccesary. but it is not now. I don't know why.  - Qinxiang *)
Qed.

Lemma memory_block_conflict: forall sh n m p,
  0 < n <= Int.max_unsigned -> 0 < m <= Int.max_unsigned ->
  memory_block sh n p * memory_block sh m p |-- FF.
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
  destruct n'; [simpl in H; omega | rewrite Nat2Z.inj_succ in H].

  remember (nat_of_Z (Int.unsigned (Int.repr m))) as m' eqn:Hm.
  rewrite Int.unsigned_repr in Hm; [| split; omega].
  rewrite <- (nat_of_Z_eq m) in H0; [|omega].
  rewrite <- Hm in H0.
  destruct m'; [simpl in H0; omega | rewrite Nat2Z.inj_succ in H0].
  simpl.
  unfold mapsto_.
  apply derives_trans with (mapsto sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr (Int.unsigned i)))
     Vundef * mapsto sh (Tint I8 Unsigned noattr) (Vptr b (Int.repr (Int.unsigned i)))
      Vundef * TT).
  rewrite <- Hn, <- Hm; simpl.
  cancel.
  apply derives_trans with (FF * TT).
  apply sepcon_derives; [|cancel].
  apply mapsto_conflict.
  normalize.
Qed.

Lemma data_at_conflict: forall sh t v v' p,
  field_compatible t nil p ->
  0 < sizeof cenv_cs t < Int.modulus ->
  data_at sh t v p * data_at sh t v' p |-- FF.
Proof.
  intros.
  eapply derives_trans.
  + apply sepcon_derives.
    apply data_at_data_at_; assumption.
    apply data_at_data_at_; assumption.
  + rewrite data_at__memory_block by auto.
    normalize.
    apply memory_block_conflict; (unfold Int.max_unsigned; omega).
Qed.

Lemma field_at_conflict: forall sh t fld p v v',
  0 < sizeof cenv_cs (nested_field_type2 t fld) < Int.modulus ->
  legal_alignas_type t = true ->
  field_at sh t fld v p * field_at sh t fld v' p|-- FF.
Proof.
  intros.
  eapply derives_trans.
  + apply sepcon_derives.
    apply field_at_field_at_; assumption.
    apply field_at_field_at_; assumption.
  + rewrite field_at__memory_block by auto.
    normalize.
    apply memory_block_conflict; (unfold Int.max_unsigned; omega).
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  0 < sizeof cenv_cs (nested_field_type2 t fld) < Int.modulus ->
  legal_alignas_type t = true ->
        field_at_ sh t fld p
        * field_at_ sh t fld p |-- FF.
Proof.
intros.
apply field_at_conflict; assumption.
Qed.

Lemma field_compatible_offset_isptr:
forall t path n c, field_compatible t path (offset_val n c) ->
          isptr c.
Proof.
intros.
destruct H as [? _]. destruct c; try contradiction; auto.
Qed.

Lemma field_compatible0_offset_isptr:
forall t path n c, field_compatible t path (offset_val n c) ->
          isptr c.
Proof.
intros.
destruct H as [? _]. destruct c; try contradiction; auto.
Qed.

Lemma is_pointer_or_null_field_address_lemma:
 forall t path p,
   is_pointer_or_null (field_address t path p) <->
   field_compatible t path p.
Proof.
intros.
unfold field_address.
if_tac; intuition.
Qed.

Lemma isptr_field_address_lemma:
 forall t path p,
   isptr (field_address t path p) <->
   field_compatible t path p.
Proof.
intros.
unfold field_address.
if_tac; intuition.
Qed.

Lemma eval_lvar_spec: forall id t rho,
  match eval_lvar id t rho with
  | Vundef => True
  | Vptr b ofs => ofs = Int.zero
  | _ => False
  end.
Proof.
  intros.
  unfold eval_lvar.
  destruct (Map.get (ve_of rho) id); auto.
  destruct p.
  if_tac; auto.
Qed.

Lemma var_block_data_at_:
  forall  sh id t, 
  legal_alignas_type t = true ->
  legal_cosu_type t = true ->
  complete_type cenv_cs t = true ->
  Z.ltb (sizeof cenv_cs t) Int.modulus = true ->
  var_block sh (id, t) = `(data_at_ sh t) (eval_lvar id t).
Proof.
  intros; extensionality rho.
 unfold var_block.
  unfold_lift.
  simpl.
  apply Zlt_is_lt_bool in H2.
  rewrite data_at__memory_block by auto.
  rewrite memory_block_isptr.
  unfold local, lift1; unfold_lift.
  unfold align_compatible.
  pose proof eval_lvar_spec id t rho.
  destruct (eval_lvar id t rho); simpl in *; normalize.
  subst.
  f_equal.
  apply ND_prop_ext.
  unfold field_compatible.
  unfold isptr, legal_nested_field, size_compatible, align_compatible.
  change (Int.unsigned Int.zero) with 0.
  rewrite Z.add_0_l.
  pose proof Z.divide_0_r (alignof cenv_cs t).
  assert (sizeof cenv_cs t <= Int.modulus) by omega.
  assert (sizeof cenv_cs t <= Int.max_unsigned) by (unfold Int.max_unsigned; omega).
  tauto.
Qed.

End CENV.

Hint Resolve field_at_compatible : saturate_local.
Hint Resolve field_at__compatible : saturate_local.
Hint Resolve data_at_compatible : saturate_local.
Hint Resolve data_at__compatible : saturate_local.
Hint Rewrite <- @field_at_offset_zero: norm.
Hint Rewrite <- @field_at__offset_zero: norm.
Hint Rewrite <- @field_at_offset_zero: cancel.
Hint Rewrite <- @field_at__offset_zero: cancel.
Hint Rewrite <- @data_at__offset_zero: norm.
Hint Rewrite <- @data_at_offset_zero: norm.
Hint Rewrite <- @data_at__offset_zero: cancel.
Hint Rewrite <- @data_at_offset_zero: cancel.

(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at_ _ _ _ _) => 
   (apply field_at_field_at_) : cancel.

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at ?sh ?t ?gfs ?v _) => 
   (change (field_at sh t gfs v) with (field_at_ sh t gfs);
    apply field_at_field_at_) : cancel.

Hint Extern 2 (field_at ?sh ?t ?gfs ?v _ |-- field_at_ _ _ _ _) => 
   (change (field_at sh t gfs v) with (field_at_ sh t gfs);
    apply derives_refl) : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- data_at_ _ _ _) =>
    (apply data_at_data_at_) : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at__memory_block_cancel) : cancel.

Hint Extern 2 (array_at _ _ _ _ _ _ _ |-- array_at_ _ _ _ _ _ _) =>
  (apply array_at_array_at_) : cancel.
Hint Extern 1 (isptr _) => (eapply field_compatible_offset_isptr; eassumption).
Hint Extern 1 (isptr _) => (eapply field_compatible0_offset_isptr; eassumption).
Hint Rewrite @is_pointer_or_null_field_address_lemma : entailer_rewrite.
Hint Rewrite @isptr_field_address_lemma : entailer_rewrite.

Global Transparent alignof. (* MOVE ME *)

Definition field_at_mark := @field_at.
Definition field_at_hide := @field_at.

Ltac find_field_at N :=
 match N with
 | S O =>  change @field_at with field_at_mark at 1;
                 change @field_at with @field_at_hide;
                 change field_at_mark with @field_at
 | S ?k => change @field_at with field_at_hide at 1;
                find_field_at k
 end.

Ltac unfold_field_at N :=
 find_field_at N;
 match goal with 
 | |- context [@field_at ?cs ?csl ?sh ?t ?gfs ?v ?p] =>
     let id := fresh "id" in evar (id: ident);
     let Heq := fresh "Heq" in
     assert (Heq: nested_field_type2 t gfs = Tstruct id noattr)
           by (unfold id; reflexivity);
     let H := fresh in 
     assert (H:= @field_at_Tstruct cs csl sh t gfs id noattr
                          v v p  Heq (JMeq_refl _));
     unfold id in H; clear Heq id;
     let FLD := fresh "FLD" in
     forget (@field_at cs csl sh t gfs v p) as FLD;
   cbv beta iota zeta delta 
     [co_members cenv_cs get_co nested_sfieldlist_at
      nested_field_offset2 nested_field_type2
      nested_field_rec
      alignof withspacer
     ] in H;
   simpl in H;
   subst FLD;
   change field_at_hide with @field_at in *
 end.
