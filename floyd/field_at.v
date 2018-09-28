Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.floyd.sublist.

Local Open Scope logic.

(************************************************

Definition of nested_reptype_structlist, field_at, array_at, data_at, nested_sfieldlist_at

************************************************)

Section CENV.

Context {cs: compspecs}.

Lemma struct_Prop_cons2:
  forall it it' m (A: ident*type -> Type)
   (P: forall it, A it -> Prop)
   (v: compact_prod (map A (it::it'::m))),
 struct_Prop (it :: it' :: m) P v =
    (P _ (fst v) /\ struct_Prop (it'::m) P (snd v)).
Proof.
intros.
destruct v. destruct it, it'.
reflexivity.
Qed.

Lemma struct_Prop_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> Prop) (P1: forall it, A1 it -> Prop) v0 v1,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) -> P1 _ (proj_struct i m v1 d1)) ->
  struct_Prop m P0 v0 -> struct_Prop m P1 v1.
Proof.
(*  unfold proj_struct, field_type, fieldlist.field_type2. *)
  intros. revert H1.
  destruct m as [| (i0, t0) m]; [simpl; auto |].
  revert i0 t0 v0 v1 H H0; induction m as [| (i1, t1) m]; intros.
  + specialize (H0 i0).
    simpl in H0.
    unfold field_type, Ctypes.field_type in H0.
    simpl in H0.
    destruct (ident_eq i0 i0); [ | congruence].
    specialize (H0 v0 v1).
    spec H0; [left; reflexivity |].
    destruct (type_eq t0 t0); [ | congruence].
    unfold eq_rect_r in H0; rewrite <- !eq_rect_eq in H0.
    simpl. auto.
  +
    revert H1.
    change (struct_Prop ((i0, t0) :: (i1, t1) :: m) P0 v0) with
      (P0 (i0, t0) (fst v0) /\ struct_Prop ((i1, t1) :: m) P0 (snd v0)).
    change (struct_Prop ((i0, t0) :: (i1, t1) :: m) P1 v1) with
      (P1 (i0, t0) (fst v1) /\ struct_Prop ((i1, t1) :: m) P1 (snd v1)).
     intro.
      rewrite fieldlist.members_no_replicate_ind in H.
      destruct H as [H H'].
       specialize (IHm i1 t1 (snd v0) (snd v1) H').
      split.
    - destruct H1 as [H1 _]; revert H1.
      specialize (H0 i0).
      unfold proj_struct in H0.
      revert H0; unfold field_type; simpl.
      destruct (ident_eq i0 i0); [ | congruence].
    destruct (type_eq t0 t0); [ | congruence].
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      intros. apply (H0 (fst v0) (fst v1)); auto.
      hnf. left; reflexivity.
    -  destruct H1 as [_ H1]; revert H1.
      apply IHm; clear IHm.
      assert (i0<>i1) by (contradict H; left; auto).
      intros.
      specialize (H0 i).
      assert (i<>i0). contradict H1. subst i0. contradiction.
      clear H H'.
      assert (field_type i ((i0, t0) :: (i1, t1) :: m) = field_type i ((i1,t1)::m))
         by (unfold field_type; simpl; rewrite if_false; auto).
      unfold proj_struct in *.
      rewrite H in H0.
      specialize (H0 d0 d1).
      spec H0; [unfold in_members; right; auto | ].
      assert (proj_compact_prod (i, field_type i ((i1, t1) :: m))
                  ((i0, t0) :: (i1, t1) :: m) v0 d0 member_dec =
                proj_compact_prod (i, field_type i ((i1, t1) :: m)) ((i1, t1) :: m)
                 (snd v0) d0 member_dec).
         clear - H1 H4.
         unfold proj_compact_prod. unfold list_rect; cbv beta iota.
         destruct (member_dec (i, field_type i ((i1, t1) :: m)) (i0,t0)); [congruence | ].
         reflexivity.
      rewrite H5 in H0; clear H5.
      assert (proj_compact_prod (i, field_type i ((i1, t1) :: m))
                  ((i0, t0) :: (i1, t1) :: m) v1 d1 member_dec =
                proj_compact_prod (i, field_type i ((i1, t1) :: m)) ((i1, t1) :: m)
                 (snd v1) d1 member_dec).
         clear - H1 H4.
         unfold proj_compact_prod. unfold list_rect; cbv beta iota.
         destruct (member_dec (i, field_type i ((i1, t1) :: m)) (i0,t0)); [congruence | ].
         reflexivity.
      rewrite H5 in H0; clear H5.
     apply H0; auto.
Qed.

Lemma struct_Prop_ext: forall m {A0 A1} (P0: forall it, A0 it -> Prop) (P1: forall it, A1 it -> Prop) v0 v1,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) = P1 _ (proj_struct i m v1 d1)) ->
  struct_Prop m P0 v0 = struct_Prop m P1 v1.
Proof.
  intros.
  apply prop_ext; split; eapply struct_Prop_ext_derives; eauto; intros; revert H2;
  erewrite H0 by auto; eauto.
Qed.

Definition field_at (sh: Share.t) (t: type) (gfs: list gfield) (v: reptype (nested_field_type t gfs)) (p: val): mpred :=
 !! (field_compatible t gfs p) &&
 at_offset (data_at_rec sh (nested_field_type t gfs) v) (nested_field_offset t gfs) p.
Arguments field_at sh t gfs v p : simpl never.

Definition field_at_ (sh: Share.t) (t: type) (gfs: list gfield) (p: val): mpred :=
  field_at sh t gfs (default_val (nested_field_type t gfs)) p.

Arguments field_at_ sh t gfs p : simpl never.

Definition data_at (sh: Share.t) (t: type) (v: reptype t) := field_at sh t nil v.

Definition data_at_ (sh: Share.t) (t: type) := field_at_ sh t nil.

Definition nested_reptype_structlist t gfs (m: members) :=
  compact_prod (map (fun it => reptype (nested_field_type t (StructField (fst it) :: gfs))) m).

Definition nested_reptype_unionlist t gfs (m: members) :=
  compact_sum (map (fun it => reptype (nested_field_type t (UnionField (fst it) :: gfs))) m).

Lemma nested_reptype_structlist_lemma: forall t gfs id a,
  nested_field_type t gfs = Tstruct id a ->
  reptype (nested_field_type t gfs) = nested_reptype_structlist t gfs (co_members (get_co id)).
Proof.
  intros.
  rewrite H, reptype_eq.
  unfold reptype_structlist, nested_reptype_structlist.
  f_equal.
  apply map_members_ext; [apply get_co_members_no_replicate |].
  intros.
  rewrite nested_field_type_ind, H.
  simpl.
  auto.
Defined.

Lemma nested_reptype_unionlist_lemma: forall t gfs id a,
  nested_field_type t gfs = Tunion id a ->
  reptype (nested_field_type t gfs) = nested_reptype_unionlist t gfs (co_members (get_co id)).
Proof.
  intros.
  rewrite H, reptype_eq.
  unfold reptype_unionlist, nested_reptype_unionlist.
  f_equal.
  apply map_members_ext; [apply get_co_members_no_replicate |].
  intros.
  rewrite nested_field_type_ind, H.
  simpl.
  auto.
Defined.

Definition nested_sfieldlist_at sh t gfs m (v: nested_reptype_structlist t gfs m) p: mpred :=
  match m with
  | nil => (!! field_compatible t gfs p) && emp
  | _ => struct_pred m (fun it v p =>
           withspacer sh
            (nested_field_offset t gfs +
              (field_offset cenv_cs (fst it) m + sizeof (field_type (fst it) m)))
            (nested_field_offset t gfs +
              field_offset_next cenv_cs (fst it) m (sizeof (nested_field_type t gfs)))
            (field_at sh t (StructField (fst it) :: gfs) v) p) v p
  end.

Definition nested_ufieldlist_at sh t gfs m (v: nested_reptype_unionlist t gfs m) (p: val): mpred :=
  match m with
  | nil => (!! field_compatible t gfs p) && emp
  | _ => union_pred m (fun it v p =>
           withspacer sh
            (nested_field_offset t gfs + sizeof (field_type (fst it) m))
            (nested_field_offset t gfs + sizeof (nested_field_type t gfs))
            (field_at sh t (UnionField (fst it) :: gfs) v) p) v p
  end.

Definition array_at (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z)
  (v: list (reptype (nested_field_type t (ArraySubsc 0 :: gfs)))) (p: val) : mpred :=
  !! (field_compatible0 t (ArraySubsc lo :: gfs) p /\
      field_compatible0 t (ArraySubsc hi :: gfs) p) &&
  array_pred lo hi
    (fun i v => at_offset (data_at_rec sh (nested_field_type t (ArraySubsc 0 :: gfs)) v)
       (nested_field_offset t (ArraySubsc i :: gfs))) v p.

Definition array_at_ (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z) : val -> mpred :=
 array_at sh t gfs lo hi (list_repeat (Z.to_nat (hi-lo)) (default_val _)).

(************************************************

field_compatible, local_facts, isptr and offset_zero properties

************************************************)

Lemma field_at_local_facts:
  forall sh t path v c,
     field_at sh t path v c |-- !! (field_compatible t path c /\ value_fits (nested_field_type t path) v).
Proof.
  intros.
  unfold field_at.
  rewrite prop_and; apply andp_derives; auto.
  unfold at_offset.
  apply data_at_rec_value_fits.
Qed.

Lemma field_at_compatible':
 forall sh t path v c,
     field_at sh t path v c =
     !! field_compatible t path c && field_at sh t path v c.
Proof.
intros.
apply pred_ext.
apply andp_right; auto.
eapply derives_trans; [apply field_at_local_facts | normalize].
normalize.
Qed.

Lemma field_at__local_facts: forall sh t gfs p,
  field_at_ sh t gfs p |-- !! field_compatible t gfs p.
Proof.
  intros.
  unfold field_at_, field_at.
 normalize.
Qed.

Lemma data_at_local_facts:
   forall sh t v p, data_at sh t v p |-- !! (field_compatible t nil p /\ value_fits t v).
Proof. intros. apply field_at_local_facts. Qed.

Lemma data_at__local_facts: forall sh t p, data_at_ sh t p |-- !! field_compatible t nil p.
Proof. intros.
  apply field_at__local_facts.
Qed.

Lemma array_at_local_facts: forall sh t gfs lo hi v p,
  array_at sh t gfs lo hi v p |--
    !! (field_compatible0 t (ArraySubsc lo :: gfs) p
        /\ field_compatible0 t (ArraySubsc hi :: gfs) p
        /\ Zlength v = hi - lo
        /\ Forall (value_fits (nested_field_type t (ArraySubsc 0 :: gfs))) v).
Proof.
  intros.
  unfold array_at.
  rewrite !prop_and.
  rewrite <- andp_assoc.
  apply andp_derives; auto.
  eapply derives_trans; [apply array_pred_local_facts |].
  + intros.
    unfold at_offset.
    instantiate (1 := fun x => value_fits _ x).
    apply data_at_rec_value_fits.
 + normalize.
Qed.

Lemma array_at__local_facts: forall sh t gfs lo hi p,
  array_at_ sh t gfs lo hi p |--
    !! (field_compatible0 t (ArraySubsc lo :: gfs) p
        /\ field_compatible0 t (ArraySubsc hi :: gfs) p).
Proof.
  intros.
  unfold array_at_.
  eapply derives_trans; [apply array_at_local_facts; eauto | ].
  apply prop_derives; intuition.
Qed.

Lemma field_at_isptr: forall sh t gfs v p,
  field_at sh t gfs v p = (!! isptr p) && field_at sh t gfs v p.
Proof. intros. eapply local_facts_isptr; [apply field_at_local_facts | intros [? ?]; auto]. Qed.

Lemma field_at_offset_zero: forall sh t gfs v p,
  field_at sh t gfs v p = field_at sh t gfs v (offset_val 0 p).
Proof. intros. apply local_facts_offset_zero.
 intros. rewrite field_at_isptr; normalize.
Qed.

Lemma field_at__isptr: forall sh t gfs p,
  field_at_ sh t gfs p = (!! isptr p) && field_at_ sh t gfs p.
Proof. intros.
 intros. eapply local_facts_isptr; [apply field_at__local_facts | intros [? ?]; auto].
Qed.

Lemma field_at__offset_zero: forall sh t gfs p,
  field_at_ sh t gfs p = field_at_ sh t gfs (offset_val 0 p).
Proof. intros. apply local_facts_offset_zero.
 intros. rewrite field_at__isptr; normalize.
Qed.

Lemma data_at_isptr: forall sh t v p, data_at sh t v p = !!(isptr p) && data_at sh t v p.
Proof. intros. eapply local_facts_isptr; [apply data_at_local_facts | intros [? ?]; auto].
Qed.

Lemma data_at_offset_zero: forall sh t v p, data_at sh t v p = data_at sh t v (offset_val 0 p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity.
    intros; rewrite data_at_isptr; normalize.
Qed.

Lemma data_at__isptr: forall sh t p, data_at_ sh t p = !!(isptr p) && data_at_ sh t p.
Proof. intros. eapply local_facts_isptr; [apply data_at__local_facts | intros [? ?]; auto].
Qed.

Lemma data_at__offset_zero: forall sh t p, data_at_ sh t p = data_at_ sh t (offset_val 0 p).
Proof. intros. apply field_at__offset_zero. Qed.

(************************************************

Ext lemmas of array_at

************************************************)

Lemma array_at_ext_derives: forall sh t gfs lo hi v0 v1 p,
  Zlength v0 = Zlength v1 ->
  (forall i u0 u1,
     lo <= i < hi ->
     JMeq u0 (Znth (i-lo) v0) ->
     JMeq u1 (Znth (i-lo) v1) ->
     field_at sh t (ArraySubsc i :: gfs) u0 p |--
     field_at sh t (ArraySubsc i :: gfs) u1 p) ->
  array_at sh t gfs lo hi v0 p |-- array_at sh t gfs lo hi v1 p.
Proof.
  intros until p. intro ZL; intros.
  unfold array_at, field_at.
  normalize.
  eapply array_pred_ext_derives.
  1: intro; omega.
  intros.
  specialize (H i).
  clear ZL.
  revert v0 v1 H.
  unfold field_at.
  rewrite nested_field_type_ArraySubsc with (i0 := i).
  intros.
  specialize (H (Znth (i - lo) v0) (Znth (i - lo) v1)).
  do 3 (spec H; [auto |]).
  rewrite !prop_true_andp in H by (apply (field_compatible_range _ lo hi); auto).
  auto.
Qed.

Lemma array_at_ext: forall sh t gfs lo hi v0 v1 p,
  Zlength v0 = Zlength v1 ->
  (forall i u0 u1,
     lo <= i < hi ->
     JMeq u0 (Znth (i-lo) v0) ->
     JMeq u1 (Znth (i-lo) v1) ->
     field_at sh t (ArraySubsc i :: gfs) u0 p =
     field_at sh t (ArraySubsc i :: gfs) u1 p) ->
  array_at sh t gfs lo hi v0 p = array_at sh t gfs lo hi v1 p.
Proof.
  intros.
  apply pred_ext; apply array_at_ext_derives; intros; auto.
  erewrite H0 by eauto; auto.
  erewrite <- H0 by eauto; auto.
Qed.

(************************************************

Unfold and split lemmas

************************************************)

Lemma field_at_Tarray: forall sh t gfs t0 n a v1 v2 p,
  legal_nested_field t gfs ->
  nested_field_type t gfs = Tarray t0 n a ->
  0 <= n ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p = array_at sh t gfs 0 n v2 p.
Proof.
  intros.
  unfold field_at, array_at.
  revert v1 v2 H2;
  rewrite (nested_field_type_ind t (ArraySubsc 0 :: gfs)).
  rewrite H0; unfold gfield_type.
  intros.
  rewrite data_at_rec_eq.
  rewrite at_offset_array_pred.
  f_equal.
  + apply ND_prop_ext.
    rewrite !field_compatible0_cons, H0.
    assert (0 <= 0 <= n) by omega.
    assert (0 <= n <= n) by omega.
    tauto.
  + apply (JMeq_trans (unfold_reptype_JMeq _ v1)) in H2.
    forget (unfold_reptype v1) as v1'.
    clear v1.
    cbv iota beta in v1'.
    apply JMeq_eq in H2.
    rewrite Z.max_r by omega.
    apply array_pred_ext.
    - subst; auto.
    - intros.
      rewrite at_offset_eq.
      rewrite <- at_offset_eq2.
      rewrite !at_offset_eq.
      rewrite (nested_field_offset_ind t (ArraySubsc i :: gfs))
        by (apply legal_nested_field0_field; simpl; unfold legal_field; rewrite H0; auto).
      rewrite H0.
      f_equal.
      subst; auto.
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

Lemma field_at_isptr':
  forall sh t path v c, field_at sh t path v c |-- !! isptr c.
Proof.
intros.
eapply derives_trans; [apply field_at_local_facts | ].
apply prop_derives; intros [? _]; auto.
Qed.

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
  | (!! _ /\ _)%logic => destruct A as [_ A]; solve_ptr p A
  | (!! field_compatible _ _ ?q) => apply (derives_trans _ _ _ (prop_derives _ _ (field_compatible_isptr _ _ _))); solve_ptr_derives
  | (!! field_compatible0 _ _ ?q) => apply (derives_trans _ _ _ (prop_derives _ _ (field_compatible0_isptr _ _ _))); solve_ptr_derives
  | (memory_block _ _ ?q) => apply (derives_trans _ _ _ (memory_block_local_facts _ _ _)); solve_ptr_derives
  | (withspacer _ _ _ ?P p) => apply withspacer_preserve_local_facts;
                                     intro p0; solve_ptr p0 (P p0)
  | (at_offset ?P _ ?q) => apply (derives_trans _ (!! isptr q));
                           [apply at_offset_preserve_local_facts; intro p0; solve_ptr p0 (P p0) |
                            solve_ptr_derives]
  | (field_at _ _ _ _ p) => apply field_at_isptr'
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

Lemma field_at_Tstruct: forall sh t gfs id a v1 v2 p,
  nested_field_type t gfs = Tstruct id a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p = nested_sfieldlist_at sh t gfs (co_members (get_co id)) v2 p.
Proof.
  intros.
  unfold field_at, nested_sfieldlist_at.
  revert v1 H0; rewrite H; intros.
  rewrite data_at_rec_eq.
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
  2:{
    replace (!!field_compatible t (StructField i :: gfs) (Vptr b (Ptrofs.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto; apply ND_prop_ext; tauto).
    simpl in n.
    rewrite H in n.
    simpl in n.
    replace (!!field_compatible t gfs (Vptr b (Ptrofs.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto; apply ND_prop_ext; tauto).
    normalize.
  }
  rewrite nested_field_offset_ind with (gfs0 := StructField i :: gfs) by auto.
  unfold gfield_offset; rewrite H.
  f_equal; [| f_equal].
  + apply ND_prop_ext.
    rewrite field_compatible_cons, H; tauto.
  + rewrite sizeof_Tstruct.
    f_equal; [| f_equal; f_equal]; omega.
  + rewrite Z.add_assoc.
    erewrite data_at_rec_type_changable; [reflexivity | |].
    - simpl.
      rewrite nested_field_type_ind.
      simpl; rewrite H.
      auto.
    - apply (proj_compact_prod_JMeq _ (i, field_type i _) (co_members (get_co id)) _ _ (unfold_reptype v1) v2); auto.
      * intros.
        rewrite nested_field_type_ind, H.
        unfold gfield_type.
        rewrite In_field_type; auto.
        apply get_co_members_no_replicate.
      * apply in_members_field_type; auto.
      * clear - H0.
        eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
Qed.

Lemma field_at_Tunion: forall sh t gfs id a v1 v2 p,
  nested_field_type t gfs = Tunion id a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p = nested_ufieldlist_at sh t gfs (co_members (get_co id)) v2 p.
Proof.
  intros.
  unfold field_at, nested_ufieldlist_at.
  revert v1 H0; rewrite H; intros.
  rewrite data_at_rec_eq.
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
     (nested_field_type t
        (UnionField (fst (i, field_type i (co_members (get_co id)))) :: gfs))).
  {
    clear - H.
    intros.
    unfold fst, snd.
    rewrite nested_field_type_ind, H.
    reflexivity.
  }
  apply union_pred_ext; [apply get_co_members_no_replicate | |].
  {
    apply compact_sum_inj_JMeq; auto.
    + intros.
      rewrite nested_field_type_ind, H.
      reflexivity.
    + eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
  }
  intros.
  destruct_ptr p.
  assert (in_members i (co_members (get_co id))).
  {
    change i with (fst (i, field_type i (co_members (get_co id)))).
    apply in_map with (f := fst).
    eapply compact_sum_inj_in; eauto.
  }
  unfold field_at, fst, snd.
  autorewrite with at_offset_db.
  unfold offset_val.
  solve_mod_modulus.
  normalize.
  destruct (legal_nested_field_dec t (UnionField i :: gfs)).
  2:{
    replace (!!field_compatible t (UnionField i :: gfs) (Vptr b (Ptrofs.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto).
    simpl in n.
    rewrite H in n.
    simpl in n.
    replace (!!field_compatible t gfs (Vptr b (Ptrofs.repr ofs)) : mpred) with (FF: mpred)
      by (apply ND_prop_ext; unfold field_compatible; tauto).
    normalize.
  }
  rewrite nested_field_offset_ind with (gfs0 := UnionField i :: gfs) by auto.
  unfold gfield_offset; rewrite H.
  f_equal; [| f_equal].
  + apply ND_prop_ext.
    rewrite field_compatible_cons, H; tauto.
  + rewrite sizeof_Tunion.
    f_equal; [| f_equal; f_equal]; omega.
  + rewrite Z.add_0_r.
    erewrite data_at_rec_type_changable; [reflexivity | |].
    - simpl.
      rewrite nested_field_type_ind.
      simpl; rewrite H.
      auto.
    - unfold proj_union.
      apply (proj_compact_sum_JMeq _ (i, field_type i (co_members (get_co id))) (co_members (get_co id)) d0 d1 (unfold_reptype v1) v2); auto.
      * intros (i0, t0) ?.
        rewrite nested_field_type_ind, H.
        simpl.
        auto.
      * eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
Qed.

Lemma array_at_len_0: forall sh t gfs i p,
  array_at sh t gfs i i nil p = !! (field_compatible0 t (ArraySubsc i :: gfs) p) && emp.
Proof.
  intros.
  unfold array_at.
  rewrite array_pred_len_0 by omega.
  apply pred_ext; normalize.
Qed.

Lemma array_at_len_1: forall sh t gfs i v v' p,
  JMeq v v' ->
  array_at sh t gfs i (i + 1) (v :: nil) p = field_at sh t (ArraySubsc i :: gfs) v' p.
Proof.
  intros.
  unfold array_at, field_at.
  rewrite array_pred_len_1 by omega.
  revert v' H.
  rewrite nested_field_type_ArraySubsc with (i0 := i).
  intros.
  apply JMeq_eq in H; rewrite H.
  f_equal.
  apply ND_prop_ext.
  rewrite field_compatible_field_compatible0'.
  reflexivity.
Qed.

Lemma split2_array_at: forall sh t gfs lo mid hi v p,
  lo <= mid <= hi ->
  Zlength v = hi - lo ->
  array_at sh t gfs lo hi v p =
  array_at sh t gfs lo mid (sublist 0 (mid-lo) v) p *
  array_at sh t gfs mid hi (sublist (mid-lo) (Zlength v) v) p.
Proof.
  intros.
  unfold array_at.
  normalize.
  apply andp_prop_ext.
  + split; [| tauto].
    intros [? ?].
    assert (field_compatible0 t (gfs SUB mid) p) by (apply (field_compatible0_range _ lo hi); auto).
    tauto.
  + intros [? ?].
    rewrite split_array_pred with (mid0 := mid) by auto.
    rewrite H0; auto.
Qed.

Lemma split3seg_array_at: forall sh t gfs lo ml mr hi v p,
  lo <= ml ->
  ml <= mr ->
  mr <= hi ->
  Zlength v = hi-lo ->
  array_at sh t gfs lo hi v p =
    array_at sh t gfs lo ml (sublist 0 (ml-lo) v) p*
    array_at sh t gfs ml mr (sublist (ml-lo) (mr-lo) v) p *
    array_at sh t gfs mr hi (sublist (mr-lo) (hi-lo) v) p.
Proof.
  intros.
  rewrite split2_array_at with (lo := lo) (mid := ml) (hi := hi) by omega.
  rewrite sepcon_assoc; f_equal.
  assert (Zlength (sublist (ml - lo) (hi - lo) v) = hi - ml).
  {
    replace (hi - ml) with (hi - lo - (ml - lo)) by omega.
    apply Zlength_sublist; omega.
  }
  rewrite H2.
  rewrite split2_array_at with (lo := ml) (mid := mr) (hi := hi) by omega.
  f_equal.
  rewrite sublist_sublist; try omega. f_equal.  f_equal; omega.
  rewrite Zlength_sublist by omega.
  rewrite sublist_sublist; try omega. f_equal.  f_equal; omega.
Qed.

Lemma split3_array_at: forall sh t gfs lo mid hi v v0 p,
  lo <= mid < hi ->
  Zlength v = hi-lo ->
  JMeq v0 (Znth (mid-lo) v) ->
  array_at sh t gfs lo hi v p =
    array_at sh t gfs lo mid (sublist 0 (mid-lo) v) p *
    field_at sh t (ArraySubsc mid :: gfs) v0 p *
    array_at sh t gfs (mid + 1) hi (sublist (mid+1-lo) (hi-lo) v) p.
Proof.
  intros.
  rename H0 into e; rename H1 into H0.
  rewrite split3seg_array_at with (ml := mid) (mr := mid + 1) by omega.
  f_equal.
  f_equal.
  replace (mid + 1 - lo) with (mid - lo + 1) by omega.
  rewrite sublist_len_1 by omega.
  rewrite array_at_len_1 with (v' :=v0); [auto |].
  apply JMeq_sym; auto.
Qed.

(************************************************

Reroot lemmas

************************************************)

Lemma field_at_data_at: forall sh t gfs v (p: val),
  field_at sh t gfs v p =
  data_at sh (nested_field_type t gfs) v (field_address t gfs p).
Proof.
  intros.
  unfold data_at, field_at.
  rewrite (nested_field_offset_ind (nested_field_type t gfs) nil) by (simpl; tauto).
  unfold field_address.
  if_tac.
  + unfold at_offset; normalize.
    rewrite prop_true_andp; [auto |].
    destruct p; try (destruct H; contradiction).
    generalize (field_compatible_nested_field t gfs (Vptr b i));
    unfold at_offset; solve_mod_modulus; intros. auto.
  + apply pred_ext; normalize. destruct H0; contradiction.
Qed.

Lemma field_at_data_at' : forall sh t gfs v p, field_at sh t gfs v p =
  !!field_compatible t gfs p &&
  data_at sh (nested_field_type t gfs) v (offset_val (nested_field_offset t gfs) p).
Proof.
  intros.
  rewrite field_at_data_at.
  unfold field_address.
  if_tac.
  - rewrite prop_true_andp; auto.
  - rewrite prop_false_andp by auto.
    rewrite data_at_isptr, prop_false_andp; auto.
Qed.

Lemma field_at__data_at_: forall sh t gfs p,
  field_at_ sh t gfs p =
  data_at_ sh (nested_field_type t gfs) (field_address t gfs p).
Proof.
  intros.
  unfold data_at_, field_at_. apply field_at_data_at.
Qed.

Lemma lifted_field_at_data_at: forall sh t gfs v p,
  `(field_at sh t gfs) v p =
  `(data_at sh (nested_field_type t gfs)) v (`(field_address t gfs) p).
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at_data_at.
Qed.

Lemma lifted_field_at__data_at_: forall sh t gfs p,
  `(field_at_ sh t gfs) p =
  `(data_at_ sh (nested_field_type t gfs)) (`(field_address t gfs) p).
Proof.
  intros.
  extensionality rho.
  unfold liftx, lift; simpl.
  apply field_at__data_at_.
Qed.

Lemma value_fits_JMeq:
  forall t t' v v',
   t=t' -> JMeq v v' -> value_fits t v -> value_fits t' v'.
Proof.
intros. subst. apply JMeq_eq in H0. subst.
auto.
Qed.

Lemma array_at_data_at: forall sh t gfs lo hi v p,
  lo <= hi ->
  array_at sh t gfs lo hi v p =
  (!! field_compatible0 t (ArraySubsc lo :: gfs) p) &&
  (!! field_compatible0 t (ArraySubsc hi :: gfs) p) &&
  at_offset (data_at sh (nested_field_array_type t gfs lo hi) v)
               (nested_field_offset t (ArraySubsc lo :: gfs)) p.
Proof.
  intros.
  unfold array_at.
  rewrite at_offset_eq.
  unfold data_at, field_at.
  change (nested_field_type (nested_field_array_type t gfs lo hi) nil)
    with (Tarray (nested_field_type t (gfs SUB 0))
           (hi - lo) (no_alignas_attr (attr_of_type (nested_field_type t gfs)))).
  rewrite data_at_rec_eq.
  rewrite <- at_offset_eq.
  normalize.
  apply andp_prop_ext.
  f_equal.
  + pose proof field_compatible0_nested_field_array t gfs lo hi p.
    tauto.
  + intros [? ?].
    rewrite at_offset_eq, <- at_offset_eq2.
    rewrite at_offset_array_pred.
    rewrite Z.max_r by omega.
    eapply array_pred_shift; [reflexivity | omega |].
    intros.
    rewrite at_offset_eq at 1.
    rewrite at_offset_eq, <- at_offset_eq2, at_offset_eq.
    f_equal.
    f_equal.
    f_equal.
    rewrite nested_field_offset_ind with (gfs0 := nil) by (apply (field_compatible0_nested_field_array t gfs lo hi p); auto).
    assert (field_compatible0 t (gfs SUB i') p)
      by (apply (field_compatible0_range _ lo hi); auto; omega).
    rewrite nested_field_offset_ind with (gfs0 := ArraySubsc i' :: _) by auto.
    rewrite nested_field_offset_ind with (gfs0 := ArraySubsc lo :: _) by auto.
    rewrite nested_field_type_ind with (gfs0 := ArraySubsc 0 :: _).
    rewrite field_compatible0_cons in H4.
    destruct (nested_field_type t gfs); try tauto.
    unfold gfield_offset, gfield_type.
    assert (sizeof t0 * i' = sizeof t0 * lo + sizeof t0 * i)%Z by (rewrite Zred_factor4; f_equal; omega).
    omega.
Qed.

Lemma array_at_data_at':
forall sh t gfs lo hi v p,
  lo <= hi ->
  field_compatible0 t (ArraySubsc lo :: gfs) p ->
  field_compatible0 t (ArraySubsc hi :: gfs) p ->
  array_at sh t gfs lo hi v p =
  data_at sh (nested_field_array_type t gfs lo hi) v
               (field_address0 t (ArraySubsc lo::gfs) p).
Proof.
  intros.
  rewrite array_at_data_at by auto.
  rewrite !prop_true_andp by auto.
  unfold at_offset.
  f_equal.
  unfold field_address0.
  rewrite if_true; auto.
Qed.

Lemma array_at_data_at'':
forall sh t gfs lo hi v p,
  lo <= hi ->
  field_compatible0 t (ArraySubsc hi :: gfs) p ->
  array_at sh t gfs lo hi v p =
  data_at sh (nested_field_array_type t gfs lo hi) v
               (field_address0 t (ArraySubsc lo::gfs) p).
Proof.
  intros.
  rewrite array_at_data_at by auto.
  unfold at_offset.
  unfold field_address0.
  if_tac.
  + rewrite !prop_true_andp by auto.
    auto.
  + apply pred_ext.
    - normalize.
    - rewrite data_at_isptr.
      normalize.
Qed.

Lemma array_at_data_at''':
  forall sh t gfs lo hi v p t0 n a,
  nested_field_type t gfs = Tarray t0 n a ->
  lo <= hi <= n ->
  array_at sh t gfs lo hi v p =
  data_at sh (nested_field_array_type t gfs lo hi) v
               (field_address0 t (ArraySubsc lo::gfs) p).
Proof.
  intros.
  destruct H0.
  rewrite array_at_data_at by auto.
  unfold at_offset.
  unfold field_address0.
  if_tac.
  + assert (field_compatible0 t (gfs SUB hi) p).
    - rewrite field_compatible0_cons in *.
      rewrite H in *.
      destruct H2 as [[? ?] ?].
      split; [split |]; auto.
      omega.
    - rewrite !prop_true_andp by auto.
      auto.
  + apply pred_ext.
    - normalize.
    - rewrite data_at_isptr.
      normalize.
Qed.
  
Lemma split3seg_array_at': forall sh t gfs lo ml mr hi v p,
  lo <= ml ->
  ml <= mr ->
  mr <= hi ->
  Zlength v = hi-lo ->
  array_at sh t gfs lo hi v p =
    array_at sh t gfs lo ml (sublist 0 (ml-lo) v) p*
    data_at sh (nested_field_array_type t gfs ml mr)
        (sublist (ml-lo) (mr-lo) v)
               (field_address0 t (ArraySubsc ml::gfs) p) *
    array_at sh t gfs mr hi (sublist (mr-lo) (hi-lo) v) p.
Proof.
  intros.
  rewrite (split3seg_array_at sh t gfs lo ml mr hi); auto.
  rewrite (add_andp _ _ (array_at_local_facts sh t gfs mr hi _ _)).
  normalize.
  apply andp_prop_ext; [tauto |].
  intros [? [? _]].
  rewrite (array_at_data_at'' sh t gfs ml mr); auto.
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
    unfold align_compatible, size_compatible in *.
    revert H f; solve_mod_modulus; intros.
    pose proof nested_field_offset_in_range t gfs.
    spec H1; [tauto |].
    spec H1; [tauto |].
    rewrite (Z.mod_small ofs) in * by omega.
    rewrite (Z.mod_small (ofs + nested_field_offset t gfs)) in H by (pose proof sizeof_pos (nested_field_type t gfs); omega).
    apply data_at_rec_data_at_rec_; try tauto.
    omega.
  + unfold field_at_, field_at.
    normalize.
Qed.

Lemma field_at_field_at_default : forall sh t gfs v v' p,
  v' = default_val (nested_field_type t gfs) ->
  field_at sh t gfs v p |-- field_at sh t gfs v' p.
Proof.
  intros; subst.
  apply field_at_field_at_.
Qed.

Lemma field_at__memory_block: forall sh t gfs p,
  field_at_ sh t gfs p =
  memory_block sh (sizeof (nested_field_type t gfs)) (field_address t gfs p).
Proof.
  intros.
  unfold field_address.
  destruct (field_compatible_dec t gfs p).
  + unfold field_at_, field_at.
    rewrite prop_true_andp by auto.
    assert (isptr p) by auto; destruct p; try contradiction; clear H. rename i into ofs.
    inv_int ofs. rename ofs0 into ofs.
    unfold at_offset, offset_val.
    solve_mod_modulus.
    pose proof field_compatible_nested_field _ _ _ f.
    revert H f;
    unfold field_compatible;
    unfold size_compatible, align_compatible, offset_val;
    solve_mod_modulus;
    intros.
    pose proof nested_field_offset_in_range t gfs.
    spec H1; [tauto |].
    spec H1; [tauto |].
    rewrite (Z.mod_small ofs) in * by omega.
    rewrite (Z.mod_small (ofs + nested_field_offset t gfs)) in H by (pose proof sizeof_pos (nested_field_type t gfs); omega).
    rewrite memory_block_data_at_rec_default_val; try tauto; try omega.
  + unfold field_at_, field_at.
    rewrite memory_block_isptr.
    apply pred_ext; normalize.
Qed.

Lemma data_at_data_at_ : forall sh t v p,
  data_at sh t v p |-- data_at_ sh t p.
Proof.
  intros.
  apply field_at_field_at_.
Qed.

Lemma data_at_data_at_default : forall sh t v v' p,
  v' = default_val (nested_field_type t nil) ->
  data_at sh t v p |-- data_at sh t v' p.
Proof.
  intros; subst.
  apply data_at_data_at_.
Qed.

Lemma data_at__memory_block: forall sh t p,
  data_at_ sh t p =
  (!! field_compatible t nil p) && memory_block sh (sizeof t) p.
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
  memory_block sh (sizeof t) p = data_at_ sh t p.
Proof.
  intros.
  rewrite data_at__memory_block.
  normalize.
Qed.

Lemma data_at__memory_block_cancel:
   forall sh t p,
       data_at_ sh t p |-- memory_block sh (sizeof t) p.
Proof.
  intros.
  rewrite data_at__memory_block.
  normalize.
Qed.

Lemma data_at_memory_block:
  forall sh t v p,
     data_at sh t v p |-- memory_block sh (sizeof t) p.
Proof.
  intros.
  eapply derives_trans; [apply data_at_data_at_; reflexivity |].
  rewrite data_at__memory_block by auto.
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
         rep_omega
       | try apply f_equal_Int_repr;
         rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l; simpl; rep_omega
       ])
    : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at_memory_block;
       [reflexivity
       | rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l;simpl;
         rep_omega
       | try apply f_equal_Int_repr;
         rewrite ?sizeof_Tarray by omega;
         rewrite ?sizeof_tuchar, ?Z.mul_1_l; simpl; rep_omega
       ])
    : cancel.
*)

Lemma array_at_array_at_: forall sh t gfs lo hi v p,
  array_at sh t gfs lo hi v p |-- array_at_ sh t gfs lo hi p.
Proof.
  intros.
  eapply derives_trans; [apply andp_right; [apply array_at_local_facts | apply derives_refl] | ].
 normalize.
  unfold array_at_.
  apply array_at_ext_derives.
  1: rewrite Zlength_list_repeat by (rewrite Zlength_correct in H1; omega); omega.
  intros.
  destruct (field_compatible0_dec t (ArraySubsc i :: gfs) p).
  + revert u1 H5; erewrite <- nested_field_type_ArraySubsc with (i0 := i); intros.
    apply JMeq_eq in H5; rewrite H5. unfold Znth. rewrite if_false by omega.
    rewrite nth_list_repeat.
    apply field_at_field_at_; auto.
  + unfold field_at.
    normalize.
    contradiction (field_compatible_field_compatible0 t (ArraySubsc i :: gfs) p H6).
Qed.

Lemma withspacer_field_at__Tunion: forall sh t gfs i id a p,
  nested_field_type t gfs = Tunion id a ->
  in_members i (co_members (get_co id)) ->
  withspacer sh
   (nested_field_offset t gfs +
    sizeof (field_type i (co_members (get_co id))))
   (nested_field_offset t gfs + sizeof (nested_field_type t gfs))
   (field_at_ sh t (gfs UDOT i)) p =
  memory_block sh (sizeof (nested_field_type t gfs)) (field_address t gfs p).
Proof.
  intros.
  rewrite withspacer_spacer.
  destruct (field_compatible_dec t gfs p).
  2:{
    unfold field_at_.
    assert (~ field_compatible t (gfs UDOT i) p) by (rewrite field_compatible_cons, H; tauto).
    rewrite field_at_compatible'.
    rewrite memory_block_isptr.
    unfold field_address.
    rewrite if_false by auto.
    rewrite H.
    apply pred_ext; normalize.
  }
  rewrite field_at__memory_block.
  assert (field_compatible t (gfs UDOT i) p) by (rewrite field_compatible_cons, H; split; auto).
  rewrite !field_compatible_field_address by auto.
  rewrite !(nested_field_offset_ind _ (gfs UDOT _)) by auto.
  unfold gfield_offset; rewrite H, Z.add_0_r.
  rewrite !(nested_field_type_ind _ (gfs UDOT _)), H.
  unfold gfield_type.
  assert (isptr p) by auto.
  destruct p; try tauto.
  inv_int i0.
  pose proof nested_field_offset_in_range t gfs as HH.
  spec HH; [auto |].
  spec HH; [unfold field_compatible in *; tauto |].
  rewrite spacer_sepcon_memory_block.
  + reflexivity.
  + pose proof sizeof_pos (field_type i (co_members (get_co id))); omega.
  + omega.
  + split.
    - rewrite sizeof_Tunion.
      erewrite co_consistent_sizeof by apply get_co_consistent.
      rewrite complete_legal_cosu_type_Tunion with (a0 := a)
        by (rewrite <- H; apply nested_field_type_complete_legal_cosu_type;
            unfold field_compatible in *; tauto).
      pose proof align_le (sizeof_composite cenv_cs Union (co_members (get_co id)))
           (co_alignof (get_co id)) (co_alignof_pos _).
      unfold sizeof_composite in *.
      pose proof sizeof_union_in_members _ _ H0.
      omega.
    - rewrite <- H.
      unfold field_compatible in *.
      unfold size_compatible in *.
      revert H1; solve_mod_modulus; intros.
      rewrite Zmod_small in H1 by omega.
      omega.
  + rewrite <- H.
    unfold field_compatible, size_compatible in *.
    rewrite Ptrofs.unsigned_repr in * by (unfold Ptrofs.max_unsigned; omega).
    omega.
Qed.

Lemma array_at_ramif: forall sh t gfs t0 n a lo hi i v v0 p,
(*  let d := default_val _ in *)
  nested_field_type t gfs = Tarray t0 n a ->
  lo <= i < hi ->
  JMeq v0 (Znth (i - lo) v) ->
  array_at sh t gfs lo hi v p |-- field_at sh t (ArraySubsc i :: gfs) v0 p *
   (ALL v0: _, ALL v0': _, !! JMeq v0 v0' -->
      (field_at sh t (ArraySubsc i :: gfs) v0 p -*
        array_at sh t gfs lo hi (upd_Znth (i - lo) v v0') p)).
Proof.
  intros.
  rewrite (add_andp _ _ (array_at_local_facts _ _ _ _ _ _ _)).
  normalize.
  rewrite allp_uncurry'.
  change (ALL  st: _,
    !!JMeq (fst st) (snd st) -->
     (field_at sh t (gfs SUB i) (fst st) p -*
      array_at sh t gfs lo hi (upd_Znth (i - lo) v (snd st)) p))
  with (allp ((fun st => !!JMeq (fst st) (snd st)) -->
               ((fun st => field_at sh t (gfs SUB i) (fst st) p) -*
                 fun st => array_at sh t gfs lo hi (upd_Znth (i - lo) v (snd st)) p))).
  eapply RAMIF_Q'.solve with
    (array_at sh t gfs lo i (sublist 0 (i - lo) v) p *
     array_at sh t gfs (i + 1) hi (sublist (i + 1 - lo) (hi - lo) v) p).
  + simpl; auto.
  + erewrite (split3_array_at sh t gfs lo i hi) by (eauto; omega).
    cancel.
  + clear v0 H1.
    intros [v0 v0'].
    normalize.
    erewrite (split3_array_at sh t gfs lo i hi).
    2: auto.
    2:{
      rewrite upd_Znth_Zlength by omega.
      auto.
    }
    2:{
      rewrite upd_Znth_same by omega.
      exact H1.
    }
    rewrite sublist_upd_Znth_l with (lo0 := 0) by omega.
    rewrite sublist_upd_Znth_r with (lo0 := (i + 1 - lo)) by omega.
    unfold fst; cancel.
Qed.

Lemma nested_sfieldlist_at_ramif: forall sh t gfs id a i v p,
  let d := default_val _ in
  nested_field_type t gfs = Tstruct id a ->
  in_members i (co_members (get_co id)) ->
  nested_sfieldlist_at sh t gfs (co_members (get_co id)) v p |--
  field_at sh t (StructField i :: gfs)
    (proj_struct i (co_members (get_co id)) v d) p *
      (ALL v0: _,
         field_at sh t (StructField i :: gfs) v0 p -*
           nested_sfieldlist_at sh t gfs (co_members (get_co id))
            (upd_struct i (co_members (get_co id)) v v0) p).
Proof.
  intros.
  destruct (co_members (get_co id)) eqn:?; [inv H0 |].
  revert v d H0; rewrite <- Heqm; intros.
  unfold nested_sfieldlist_at.
  pattern (co_members (get_co id)) at 1 7; rewrite Heqm.

  match goal with
  | |- _ |-- _ * (ALL v0: _, ?A1 v0 p -* ?A2 (?A3 v0) p) =>
      change (ALL v0: _, A1 v0 p -* A2 (A3 v0) p)
      with (allp (Basics.compose (fun P => P p) (fun v0 => A1 v0) -*
                  Basics.compose (fun v0 => A2 (A3 v0) p) (fun v0 => v0)))
  end.

  Opaque struct_pred. eapply @RAMIF_Q.trans. Transparent struct_pred.
  2:{
    apply (struct_pred_ramif (co_members (get_co id))
            (fun it v p =>
              withspacer sh
                (nested_field_offset t gfs +
                (field_offset cenv_cs (fst it) (co_members (get_co id)) +
                 sizeof (field_type (fst it) (co_members (get_co id)))))
                (nested_field_offset t gfs +
                 field_offset_next cenv_cs (fst it) (co_members (get_co id))
                   (sizeof (nested_field_type t gfs)))
                (field_at sh t (gfs DOT fst it) v) p)); auto.
    apply get_co_members_no_replicate.
  }
  2:{
    apply withspacer_ramif_Q.
  }
  intros.
  apply derives_refl.
Qed.

Lemma nested_ufieldlist_at_ramif: forall sh t gfs id a i v p,
  let d := default_val _ in
  nested_field_type t gfs = Tunion id a ->
  in_members i (co_members (get_co id)) ->
  nested_ufieldlist_at sh t gfs (co_members (get_co id)) v p |--
  field_at sh t (UnionField i :: gfs)
    (proj_union i (co_members (get_co id)) v d) p *
      (ALL v0: _,
         field_at sh t (UnionField i :: gfs) v0 p -*
           nested_ufieldlist_at sh t gfs (co_members (get_co id))
            (upd_union i (co_members (get_co id)) v v0) p).
Proof.
  intros.
  destruct (co_members (get_co id)) eqn:?; [inv H0 |].
  revert v d H0; rewrite <- Heqm; intros.
  unfold nested_ufieldlist_at.
  pattern (co_members (get_co id)) at 1 5; rewrite Heqm.

  match goal with
  | |- _ |-- _ * (ALL v0: _, ?A1 v0 p -* ?A2 (?A3 v0) p) =>
      change (ALL v0: _, A1 v0 p -* A2 (A3 v0) p)
      with (allp (Basics.compose (fun P => P p) (fun v0 => A1 v0) -*
                  Basics.compose (fun v0 => A2 (A3 v0) p) (fun v0 => v0)))
  end.

  Opaque union_pred. eapply @RAMIF_Q.trans. Transparent union_pred.
  2:{
    apply (union_pred_ramif (co_members (get_co id))
            (fun it v p =>
              withspacer sh
                (nested_field_offset t gfs +
                 sizeof
                   (field_type (fst it) (co_members (get_co id))))
                (nested_field_offset t gfs +
                 sizeof (nested_field_type t gfs))
                (field_at sh t (gfs UDOT fst it) v) p)); auto.
    2: apply get_co_members_no_replicate.
    instantiate (1 := default_val _).
    intros.
    rewrite !withspacer_spacer.
    unfold fst.
    fold (field_at_ sh t (gfs UDOT i) p).
    eapply derives_trans; [eapply sepcon_derives; [apply derives_refl | apply field_at_field_at_] |].
    rewrite <- !withspacer_spacer.
    erewrite !withspacer_field_at__Tunion by eauto.
    apply derives_refl.
  }
  2:{
    unfold fst.
    apply withspacer_ramif_Q.
  }
  intros.
  apply derives_refl.
Qed.

Lemma memory_block_valid_ptr:
  forall sh n p,
     sepalg.nonidentity sh ->
     n > 0 ->
     memory_block sh n p |-- valid_pointer p.
Proof.
  intros.
  rewrite memory_block_isptr.
  normalize.
  destruct p; try tauto.
  inv_int i.
  replace (Vptr b (Ptrofs.repr ofs)) with (offset_val 0 (Vptr b (Ptrofs.repr ofs))) at 2.
  + apply memory_block_valid_pointer with (i := 0); auto; omega.
  + simpl.
    rewrite ptrofs_add_repr, Z.add_0_r.
    auto.
Qed.

Lemma data_at_valid_ptr:
  forall sh t v p,
     sepalg.nonidentity sh ->
     sizeof t > 0 ->
     data_at sh t v p |-- valid_pointer p.
Proof.
  intros.
  eapply derives_trans; [apply data_at_data_at_ |].
  rewrite data_at__memory_block.
  normalize.
  apply memory_block_valid_ptr; auto.
Qed.

Lemma field_at_valid_ptr:
  forall sh t path v p,
     sepalg.nonidentity sh ->
     sizeof (nested_field_type t path) > 0 ->
     field_at sh t path v p |-- valid_pointer (field_address t path p).
Proof.
intros.
rewrite field_at_data_at.
apply data_at_valid_ptr; auto.
Qed.

Lemma field_at_valid_ptr0:
  forall sh t path v p,
     sepalg.nonidentity sh ->
     sizeof (nested_field_type t path) > 0 ->
     nested_field_offset t path = 0 ->
     field_at sh t path v p |-- valid_pointer p.
Proof.
intros.
assert_PROP (field_compatible t path p).
unfold field_at.
normalize.
pattern p at 2; replace p with (field_address t path p).
rewrite field_at_data_at.
apply data_at_valid_ptr; auto.
unfold field_address. rewrite if_true by auto.
rewrite H1.
normalize.
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
    destruct (nested_field_type t gfs), gf; inversion H; subst;
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


Lemma compute_legal_nested_field_spec':
  forall t gfs,
  Forall Datatypes.id (compute_legal_nested_field t gfs) ->
  legal_nested_field t gfs.
Proof.
  intros.
  induction gfs as [| gf gfs].
  + simpl; auto.
  +  simpl in H|-*.
    unfold legal_field. unfold nested_field_type in *.
    destruct (nested_field_rec t gfs) as [[? ?] | ].
    destruct t0; try now inv H; contradiction.
    destruct gf; try now inv H; contradiction.
    inv H. split; auto.
    destruct gf; try now inv H; contradiction.
   destruct (compute_in_members i0 (co_members (get_co i))) eqn:?;
     try now inv H; contradiction.
   split; auto.
   rewrite <- compute_in_members_true_iff; auto.
    destruct gf; try now inv H; contradiction.
   destruct (compute_in_members i0 (co_members (get_co i))) eqn:?;
     try now inv H; contradiction.
   split; auto.
   rewrite <- compute_in_members_true_iff; auto.
   inv H. contradiction.
Qed.

Definition compute_legal_nested_field0 (t: type) (gfs: list gfield) : list Prop :=
  match gfs with
  | nil => nil
  | gf :: gfs0 =>
    match (nested_field_type t gfs0), gf with
    | Tarray _ n _, ArraySubsc i =>
       (0 <= i <= n) :: compute_legal_nested_field t gfs0
    | Tstruct id _, StructField i =>
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs else False :: nil
    | Tunion id _, UnionField i =>
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs else False :: nil
    | _, _ => False :: nil
    end
  end.

Lemma compute_legal_nested_field0_spec':
  forall t gfs,
  Forall Datatypes.id (compute_legal_nested_field0 t gfs) ->
  legal_nested_field0 t gfs.
Proof.
intros.
destruct gfs; simpl in *.
auto.
     unfold nested_field_type in *.
    destruct (nested_field_rec t gfs) as [[? ?] | ].
    destruct t0; try now inv H; contradiction.
    destruct g; try now inv H; contradiction.
    inv H. split.
    apply compute_legal_nested_field_spec'; auto.
    apply H2.
    destruct g; try now inv H; contradiction.
   destruct (compute_in_members i0 (co_members (get_co i))) eqn:?;
     try now inv H; contradiction.
   split.
    apply compute_legal_nested_field_spec'; auto.
   hnf.   rewrite compute_in_members_true_iff in Heqb. apply Heqb.
    destruct g; try now inv H; contradiction.
   destruct (compute_in_members i0 (co_members (get_co i))) eqn:?;
     try now inv H; contradiction.
   split.
    apply compute_legal_nested_field_spec'; auto.
   hnf.   rewrite compute_in_members_true_iff in Heqb. apply Heqb.
  inv H. contradiction.
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
  rewrite data_at_rec_at_offset';
   [ rewrite at_offset'_eq; [| rewrite <- data_at_rec_offset_zero; reflexivity]
   | apply nested_field_type2_nest_pred; simpl; auto
   | apply nested_field_offset2_type2_divide; auto].
  rewrite data_at_rec_at_offset' with (pos := (nested_field_offset2 (nested_field_type2 t gfs0) gfs1));
   [ rewrite at_offset'_eq; [| rewrite <- data_at_rec_offset_zero; reflexivity]
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

Lemma field_at_conflict: forall sh t fld p v v',
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) ->
  field_at sh t fld v p * field_at sh t fld v' p|-- FF.
Proof.
  intros.
  rewrite field_at_compatible'. normalize.
  destruct H1 as [? [? [? [? ?]]]].
  destruct (nested_field_offset_in_range t fld H5 H2).
  assert (0 < sizeof (nested_field_type t fld) < Ptrofs.modulus).
  {
    destruct p; inv H1.
    simpl in H3.
    inv_int i.
    omega.
  }
  clear - H H1 H8.  
  eapply derives_trans.
  + apply sepcon_derives.
    apply field_at_field_at_; try assumption; auto.
    apply field_at_field_at_; try assumption; auto.
  + fold (field_at_ sh t fld p).
    rewrite field_at__memory_block by auto.
    normalize.
    apply memory_block_conflict; try  (unfold Ptrofs.max_unsigned; omega).
    apply sepalg.nonidentity_nonunit; auto.
Qed.

Lemma data_at_conflict: forall sh t v v' p,
  sepalg.nonidentity sh ->
  0 < sizeof t ->
  data_at sh t v p * data_at sh t v' p |-- FF.
Proof.
  intros. unfold data_at. apply field_at_conflict; auto.
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  sepalg.nonidentity sh ->
  0 < sizeof (nested_field_type t fld) ->
        field_at_ sh t fld p
        * field_at_ sh t fld p |-- FF.
Proof.
intros.
apply field_at_conflict; auto.
Qed.

Lemma sepcon_FF_derives':
  forall (P Q: mpred), Q |-- FF -> P * Q |-- FF.
Proof.
intros.
eapply derives_trans. apply sepcon_derives; try eassumption; eauto.
rewrite sepcon_FF. auto.
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
  | Vptr b ofs => ofs = Ptrofs.zero
  | _ => False
  end.
Proof.
  intros.
  unfold eval_lvar.
  destruct (Map.get (ve_of rho) id); auto.
  destruct p.
  destruct (eqb_type _ _); auto.
Qed.

Lemma var_block_data_at_:
  forall  sh id t,
  complete_legal_cosu_type t = true ->
  Z.ltb (sizeof t) Ptrofs.modulus = true ->
  is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true ->
  readable_share sh ->
  var_block sh (id, t) = `(data_at_ sh t) (eval_lvar id t).
Proof.
  intros; extensionality rho.
  unfold var_block.
  unfold_lift.
  simpl.
  apply Zlt_is_lt_bool in H0.
  rewrite data_at__memory_block; try auto.
  rewrite memory_block_isptr.
  unfold local, lift1; unfold_lift.
  pose proof eval_lvar_spec id t rho.
  destruct (eval_lvar id t rho); simpl in *; normalize.
  subst.
  f_equal.
  apply ND_prop_ext.
  unfold field_compatible.
  unfold isptr, legal_nested_field, size_compatible, align_compatible.
  change (Ptrofs.unsigned Ptrofs.zero) with 0.
  rewrite Z.add_0_l.
  assert (sizeof t <= Ptrofs.modulus) by omega.
  assert (sizeof t <= Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; omega).
  apply la_env_cs_sound in H1; tauto.
Qed.

End CENV.

Hint Extern 2 (memory_block _ _ _ |-- valid_pointer _) =>
  (apply memory_block_valid_ptr; [auto with valid_pointer | rep_omega]) : valid_pointer.

Ltac field_at_conflict z fld :=
eapply derives_trans with FF; [ | apply FF_left];
 rewrite <- ?sepcon_assoc;
 unfold data_at_, data_at, field_at_;
 let x := fresh "x" in set (x := field_at _ _ fld _ z); pull_right x;
 let y := fresh "y" in set (y := field_at _ _ fld _ z); pull_right y;
 try (rewrite sepcon_assoc; eapply sepcon_FF_derives');
 subst x y;
 apply field_at_conflict; auto;
 try solve [simpl; computable].

Ltac data_at_conflict z := field_at_conflict z (@nil gfield).

Ltac data_at_conflict_neq_aux1 A sh fld E x y :=
   match A with
   | context [data_at sh _ _ y] => unify fld (@nil gfield)
   | context [data_at_ sh _ y]  => unify fld (@nil gfield)
   | context [field_at sh _ fld _ y] => idtac
   | context [field_at_ sh _ fld y]  => idtac
   end;
   apply derives_trans with (!! (~ E) && A);
   [apply andp_right; [ | apply derives_refl];
    let H := fresh in
    apply not_prop_right; intro H; 
    (rewrite H || rewrite (ptr_eq_e _ _ H)); 
    field_at_conflict y fld 
   | apply derives_extract_prop;
     let H1 := fresh in intro H1;
     rewrite (eq_True _ H1)
    ].

Ltac data_at_conflict_neq_aux2 A E x y :=
   match A with
   | context [data_at ?sh _ _ x] => data_at_conflict_neq_aux1 A sh (@nil gfield) E x y
   | context [data_at_ ?sh _ x]  => data_at_conflict_neq_aux1 A sh (@nil gfield) E x y
   | context [field_at ?sh _ ?fld _ x] => data_at_conflict_neq_aux1 A sh fld E x y
   | context [field_at_ ?sh _ ?fld x]  => data_at_conflict_neq_aux1 A sh fld E x y
   end.

Ltac data_at_conflict_neq :=
  match goal with |- ?A |-- ?B =>
   match B with
   | context [?x <> ?y] => data_at_conflict_neq_aux2 A (x=y) x y
   | context [~ ptr_eq ?x ?y] => data_at_conflict_neq_aux2 A (ptr_eq x y) x y
   end
  end.

Definition natural_aligned {cs: compspecs} (na: Z) (t: type): bool := (na mod (hardware_alignof ha_env_cs t) =? 0) && is_aligned cenv_cs ha_env_cs la_env_cs t 0.

Definition natural_aligned_soundness {cs: compspecs}: Prop :=
    forall na ofs t,
      complete_legal_cosu_type t = true ->
      natural_aligned na t = true ->
      (na | ofs) ->
      align_compatible_rec cenv_cs t ofs.

Lemma natural_aligned_sound {cs: compspecs}:
  natural_aligned_soundness.
Proof.
  intros.
  hnf.
  intros.
  unfold natural_aligned in H0.
  autorewrite with align in H0.
    2: eapply hardware_alignof_two_p; [exact cenv_consistent | exact ha_env_cs_consistent | exact ha_env_cs_complete].
  destruct H0.
  apply la_env_cs_sound in H2; auto.
  replace ofs with (ofs - 0) in H1 by omega.
  eapply align_compatible_rec_hardware_alignof_divide; auto.
  + exact cenv_consistent.
  + exact cenv_legal_su.
  + exact ha_env_cs_consistent.
  + exact ha_env_cs_complete.
  + eapply Z.divide_trans; eassumption.
  + exact H2.
Qed.

Definition natural_alignment := 8.

(* TODO: change this name to malloc_compatible_ptr and merge the definition of isptr, size_compatible, align_compatible into something like: size_align_compatible_ptr *)
Definition malloc_compatible (n: Z) (p: val) : Prop :=
  match p with
  | Vptr b ofs => (natural_alignment | Ptrofs.unsigned ofs) /\
                           Ptrofs.unsigned ofs + n < Ptrofs.modulus
  | _ => False
  end.

(* TODO: move these definitions and lemmas into a new file. *)
Lemma malloc_compatible_field_compatible:
  forall (cs: compspecs) t p,
     malloc_compatible (sizeof t) p ->
     complete_legal_cosu_type t = true ->
     natural_aligned natural_alignment t = true ->
     field_compatible t nil p.
Proof.
intros.
destruct p; simpl in *; try contradiction.
destruct H.
eapply natural_aligned_sound in H; eauto.
pose proof (Ptrofs.unsigned_range i).
repeat split; simpl; auto; try omega.
Qed.

Hint Extern 2 (field_compatible _ nil _) =>
 (apply malloc_compatible_field_compatible;
  [assumption | reflexivity | reflexivity]).

Lemma data_array_at_local_facts {cs: compspecs}:
 forall t' n a sh (v: list (reptype t')) p,
  data_at sh (Tarray t' n a) v p |--
  !! (field_compatible (Tarray t' n a) nil p
     /\ Zlength v = Z.max 0 n
     /\ Forall (value_fits t') v).
Proof.
intros.
eapply derives_trans; [apply data_at_local_facts |].
apply prop_derives.
intros [? ?]; split; auto.
Qed.

Lemma data_array_at_local_facts' {cs: compspecs}:
 forall t' n a sh (v: list (reptype t')) p,
  n >= 0 ->
  data_at sh (Tarray t' n a) v p |--
  !! (field_compatible (Tarray t' n a) nil p
     /\ Zlength v = n
     /\ Forall (value_fits t') v).
Proof.
intros.
eapply derives_trans; [apply data_array_at_local_facts |].
apply prop_derives.
intros [? [? ?]]; split3; auto.
rewrite Z.max_r in H1 by omega. auto.
Qed.

Lemma value_fits_by_value {cs: compspecs}:
  forall t v,
   type_is_volatile t = false ->
   type_is_by_value t = true ->
   value_fits t v = tc_val' t (repinject t v).
Proof.
intros.
rewrite value_fits_eq; destruct t; inv H; inv H0;
simpl; rewrite H2; auto.
Qed.

Ltac field_at_saturate_local :=
unfold data_at;
match goal with |- field_at ?sh ?t ?path ?v ?c |-- _ =>
eapply derives_trans; [apply field_at_local_facts |];
  cbv beta;
  try rewrite proj_sumbool_is_true by auto;
  try rewrite proj_sumbool_is_false by auto;
  let p := fresh "p" in set (p := nested_field_type t path);
  simpl in p; unfold field_type in p; simpl in p; subst p;
  try rewrite value_fits_by_value by reflexivity;
  try match goal with |- context [repinject ?t ?v] =>
    change (repinject t v) with v
  end;
  apply derives_refl
end.

Ltac data_at_valid_aux :=
 simpl sizeof; rewrite ?Z.max_r by rep_omega; rep_omega.

Hint Extern 1 (data_at _ _ _ _ |-- valid_pointer _) =>
    (simple apply data_at_valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

Hint Extern 1 (field_at _ _ _ _ _ |-- valid_pointer _) =>
    (simple apply field_at_valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

Hint Extern 1 (data_at_ _ _ _ |-- valid_pointer _) =>
    (unfold data_at_, field_at_; 
     simple apply field_at_valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

Hint Extern 1 (field_at_ _ _ _ _ |-- valid_pointer _) =>
    (unfold field_at_; simple apply field_at_valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

(* Hint Resolve data_at_valid_ptr field_at_valid_ptr field_at_valid_ptr0 : valid_pointer. *)

(*Hint Resolve field_at_local_facts : saturate_local.*)
Hint Extern 1 (field_at _ _ _ _ _ |-- _) =>
 (field_at_saturate_local) : saturate_local.

(* Hint Resolve data_at_local_facts : saturate_local.*)
Hint Extern 1 (data_at _ _ _ _ |-- _) =>
 (field_at_saturate_local) : saturate_local.

Hint Resolve @array_at_local_facts @array_at__local_facts : saturate_local.


Hint Resolve field_at__local_facts : saturate_local.
Hint Resolve data_at__local_facts : saturate_local.
Hint Extern 0 (data_at _ (Tarray _ _ _) _ _ |-- _) =>
  (apply data_array_at_local_facts'; omega) : saturate_local.
Hint Extern 0 (data_at _ (tarray _ _) _ _ |-- _) =>
  (apply data_array_at_local_facts'; omega) : saturate_local.
Hint Extern 1 (data_at _ (Tarray _ _ _) _ _ |-- _) =>
  (apply data_array_at_local_facts) : saturate_local.
Hint Extern 1 (data_at _ (tarray _ _) _ _ |-- _) =>
  (apply data_array_at_local_facts) : saturate_local.
Hint Rewrite <- @field_at_offset_zero: norm1.
Hint Rewrite <- @field_at__offset_zero: norm1.
Hint Rewrite <- @field_at_offset_zero: cancel.
Hint Rewrite <- @field_at__offset_zero: cancel.
Hint Rewrite <- @data_at__offset_zero: norm1.
Hint Rewrite <- @data_at_offset_zero: norm1.
Hint Rewrite <- @data_at__offset_zero: cancel.
Hint Rewrite <- @data_at_offset_zero: cancel.


(* We do these as specific lemmas, rather than
  as Hint Resolve derives_refl, to limit their application
  and make them fail faster *)

Lemma data_at_cancel:
  forall {cs: compspecs} sh t v p,
    data_at sh t v p |-- data_at sh t v p.
Proof. intros. apply derives_refl. Qed.
Lemma field_at_cancel:
  forall {cs: compspecs} sh t gfs v p,
    field_at sh t gfs v p |-- field_at sh t gfs v p.
Proof. intros. apply derives_refl. Qed.

Lemma data_at_field_at_cancel:
  forall {cs: compspecs} sh t v p,
    data_at sh t v p |-- field_at sh t nil v p.
Proof. intros. apply derives_refl. Qed.
Lemma field_at_data_at_cancel:
  forall {cs: compspecs} sh t v p,
    field_at sh t nil v p |-- data_at sh t v p.
Proof. intros. apply derives_refl. Qed.

Hint Resolve data_at_cancel field_at_cancel
   data_at_field_at_cancel field_at_data_at_cancel : cancel.

Lemma field_at__data_at__cancel:
  forall {cs: compspecs} sh t p,
   field_at_ sh t nil p |-- data_at_ sh t p.
Proof. intros. apply derives_refl. Qed.

Lemma data_at__field_at__cancel:
  forall {cs: compspecs} sh t p,
   data_at_ sh t p |-- field_at_ sh t nil p.
Proof. intros. apply derives_refl. Qed.
Hint Resolve  field_at__data_at__cancel data_at__field_at__cancel : cancel.


(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at_ _ _ _ _) =>
   (simple apply field_at_field_at_) : cancel.

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at _ _ _ _ _) =>
  (simple apply field_at_field_at_default;
   match goal with |- _ = default_val _ => reflexivity end) : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- data_at_ _ _ _) =>
    (simple apply data_at_data_at_) : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at__memory_block_cancel) : cancel.

Hint Extern 2 (data_at _ _ _ _ |-- data_at _ _ _ _) =>
  (simple apply data_at_data_at_default;
   match goal with |- _ = default_val _ => reflexivity end) : cancel.

(* too slow this way.
Hint Extern 2 (data_at _ _ _ _ |-- data_at _ _ _ _) =>
  (apply data_at_data_at_default; reflexivity) : cancel.
*)

Hint Extern 2 (array_at _ _ _ _ _ _ _ |-- array_at_ _ _ _ _ _ _) =>
  (simple apply array_at_array_at_) : cancel.
Hint Extern 1 (isptr _) => (eapply field_compatible_offset_isptr; eassumption).
Hint Extern 1 (isptr _) => (eapply field_compatible0_offset_isptr; eassumption).
Hint Rewrite @is_pointer_or_null_field_address_lemma : entailer_rewrite.
Hint Rewrite @isptr_field_address_lemma : entailer_rewrite.

Global Transparent alignof. (* MOVE ME *)

Ltac simplify_project_default_val :=
match goal with
  | |- context [@fst ?A ?B (?x, ?y)] =>
         change (@fst A B (x,y)) with x
  | |- context [@snd ?A ?B (?x, ?y)] =>
         change (@snd A B (x,y)) with y
  | |- context [fst (@default_val ?cs ?t)] =>
  let E := fresh "E" in let D := fresh "D" in let H := fresh in
   set (E := fst (@default_val cs t));
   set (D := @default_val cs t) in E;
   unfold compact_prod_sigT_type in E; simpl in E;
   assert (H := @default_val_eq cs t);
   simpl in H;
   match type of H with
      @eq (@reptype cs t) _ (@fold_reptype _ _ (@pair ?A ?B ?x ?y)) =>
   change (@reptype cs t) with (@prod A B) in *;
   change (@default_val cs t) with (x,y) in *
   end;
   clear H; subst D; simpl in E; subst E
 | |- context [snd (@default_val ?cs ?t)] =>
  let E := fresh "E" in let D := fresh "D" in let H := fresh in
   set (E := snd (@default_val cs t));
   set (D := @default_val cs t) in E;
   unfold compact_prod_sigT_type in E; simpl in E;
   assert (H := @default_val_eq cs t);
   simpl in H;
   match type of H with
      @eq (@reptype cs t) _ (@fold_reptype _ _ (@pair ?A ?B ?x ?y)) =>
   change (@reptype cs t) with (@prod A B) in *;
   change (@default_val cs t) with (x,y) in *
   end;
   clear H; subst D; simpl in E; subst E
end.

Definition field_at_mark := @field_at.
Definition field_at_hide := @field_at.
Definition data_at_hide := @data_at.

Ltac find_field_at N :=
 match N with
 | S O =>  change @field_at with field_at_mark at 1;
              change field_at_hide with @field_at
 | S ?k => change @field_at with field_at_hide at 1;
                find_field_at k
 end.

Ltac find_data_at N :=
 match N with
 | S O =>  match goal with |- context[@data_at ?cs ?sh ?t] =>
                 change (@data_at cs sh t) with (field_at_mark cs sh t nil) at 1
                 end;
                 change data_at_hide with @data_at
 | S ?k => change @data_at with data_at_hide at 1;
                find_data_at k
 end.

Definition protect (T: Type) (x: T) := x.
Global Opaque protect.

Ltac unfold_field_at' :=
 match goal with
 | |- context [field_at_mark ?cs ?sh ?t ?gfs ?v ?p] =>
     let F := fresh "F" in
       set (F := field_at_mark cs sh t gfs v p);
       change field_at_mark with @field_at in F;
     let V := fresh "V" in set (V:=v) in F;
     let P := fresh "P" in set (P:=p) in F;
     let T := fresh "T" in set (T:=t) in F;
     let id := fresh "id" in evar (id: ident);
     let Heq := fresh "Heq" in
     assert (Heq: nested_field_type T gfs = Tstruct id noattr)
           by (unfold id,T; reflexivity);
     let H := fresh in
     assert (H:= @field_at_Tstruct cs sh T gfs id noattr
                          V V P  (eq_refl _) (JMeq_refl _));
     unfold id in H; clear Heq id;
     fold F in H; clearbody F;
     simpl co_members in H;
     lazy beta iota zeta delta  [nested_sfieldlist_at ] in H;
     change (@field_at cs sh T) with (@field_at cs sh t) in H;
     hnf in T; subst T;
     change v with (protect _ v) in V;
     simpl in H;
     unfold withspacer in H; simpl in H;
     change (protect _ v) with v in V;
     subst V;
     repeat match type of H with
     | context[fst (?A,?B)] => change (fst (A,B)) with A in H
     | context[snd (?A,?B)] => change (snd (A,B)) with B in H
     end;
     subst P;
     subst F;
     cbv beta;
     repeat flatten_sepcon_in_SEP;
     repeat simplify_project_default_val
 end.

Ltac unfold_field_at N  :=
  find_field_at N; unfold_field_at'.

Ltac unfold_data_at N  :=
  find_data_at N; unfold_field_at'.

Lemma field_at_ptr_neq{cs: compspecs} :
   forall sh t fld p1 p2 v1 v2,
  sepalg.nonidentity sh ->
   0 < sizeof (nested_field_type t (fld :: nil))  ->
   field_at sh t (fld::nil) v1 p1 *
   field_at sh t (fld::nil) v2 p2
   |--
   !! (~ ptr_eq p1 p2).
Proof.
   intros.
   apply not_prop_right; intros.
  rewrite -> (ptr_eq_e _ _ H1).   
   apply field_at_conflict; try assumption.
Qed.

Lemma field_at_ptr_neq_andp_emp{cs: compspecs} :
    forall sh t fld p1 p2 v1 v2,
  sepalg.nonidentity sh ->
 0 < sizeof (nested_field_type t (fld :: nil))  ->
   field_at sh t (fld::nil) v1 p1 *
   field_at sh t (fld::nil) v2 p2
   |--
   field_at sh t (fld::nil) v1 p1 *
   field_at sh t (fld::nil) v2 p2 *
   (!! (~ ptr_eq p1 p2) && emp).
Proof.
   intros.
   normalize.
   apply andp_right.
   apply field_at_ptr_neq; assumption.
   cancel.
Qed.

Lemma field_at_ptr_neq_null{cs: compspecs} :
   forall sh t fld v p,
   field_at sh t fld v p |-- !! (~ ptr_eq p nullval).
Proof.
   intros.
   rewrite -> field_at_isptr.
  normalize. apply prop_right.
   destruct p; unfold nullval; simpl in *; tauto.
Qed.

Lemma spacer_share_join:
  forall sh1 sh2 sh J K q,
   sepalg.join sh1 sh2 sh ->
   spacer sh1 J K q * spacer sh2 J K q = spacer sh J K q.
Proof.
 intros.
 unfold spacer.
  if_tac. normalize.
 unfold at_offset.
  apply memory_block_share_join; auto.
Qed.

Lemma struct_pred_cons2:
  forall it it' m (A: ident*type -> Type)
   (P: forall it, A it -> val -> mpred)
   (v: compact_prod (map A (it::it'::m)))
   (p: val),
 struct_pred (it :: it' :: m) P v p =
    P _ (fst v) p * struct_pred (it'::m) P (snd v) p.
Proof.
intros.
destruct v. destruct it, it'. reflexivity.
Qed.

Lemma union_pred_cons2:
  forall it it' m (A: ident*type -> Type)
   (P: forall it, A it -> val -> mpred)
   (v: compact_sum (map A (it::it'::m)))
   (p: val),
 union_pred (it :: it' :: m) P v p =
   match v with inl v => P _ v p | inr v => union_pred (it'::m) P v p end.
Proof.
intros.
destruct v, it, it'; reflexivity.
Qed.

Lemma data_at_rec_void:
  forall {cs: compspecs}
      sh t v q, t = Tvoid -> data_at_rec sh t v q = FF.
Proof.
 intros; subst; reflexivity.
Qed.

Lemma snd_reptype_structlist_aux  {cs: compspecs}:
  forall (p: ident * type) (m: list (ident * type)),
   members_no_replicate (p :: m) = true ->
  map (fun it : ident * type => reptype (field_type (fst it) (p :: m))) m =
  map (fun it : ident * type => reptype (field_type (fst it) m)) m.
  (* not useful? *)
Proof.
intros.
change (p::m) with ((p::nil) ++ m) in *.
forget (p::nil) as q.
clear p.
revert q H; induction m; intros.
reflexivity.
simpl; f_equal.
+
clear - H.
induction q. reflexivity.
simpl in H.
destruct a0.
rewrite fieldlist.members_no_replicate_ind in H.
destruct H.
rewrite <- IHq; auto.
unfold field_type. simpl.
rewrite if_false; auto.
clear - H.
contradict H. subst.
induction q. left; auto.
right. auto.
+
generalize (IHm (q++ a::nil)).
rewrite app_ass; simpl; intro.
rewrite H0.
symmetry; apply (IHm (a::nil)).
simpl.
clear - H.
induction q. auto. apply IHq.
rewrite fieldlist.members_no_replicate_ind in H.
destruct a0, H; auto.
auto.
Qed.

(*
(* TODO: remove this lemma? It is not used anywhere. *)
Lemma readable_share_join:
  forall sh1 sh2 sh,
    sepalg.join sh1 sh2 sh ->
    readable_share sh1 -> readable_share sh.
Proof.
intros.
unfold readable_share in *.
destruct H.
subst sh.
rewrite Share.distrib1.
unfold nonempty_share, sepalg.nonidentity in *.
contradict H0.
apply identity_share_bot in H0.
*)

Lemma field_at_share_join{cs: compspecs}:
  forall sh1 sh2 sh t gfs v p,
    sepalg.join sh1 sh2 sh ->
   field_at sh1 t gfs v p * field_at sh2 t gfs v p = field_at sh t gfs v p.
Proof.
intros.
unfold field_at.
normalize.
apply andp_prop_ext; [tauto |].
intros.
unfold at_offset.
destruct H0 as [? _].
assert (isptr p) by (destruct H0; tauto).
destruct p; try inversion H1.
apply data_at_rec_share_join; auto.
Qed.

Lemma field_at__share_join{cs: compspecs}:
  forall sh1 sh2 sh t gfs p,
    sepalg.join sh1 sh2 sh ->
   field_at_ sh1 t gfs p * field_at_ sh2 t gfs p = field_at_ sh t gfs p.
Proof. intros. apply field_at_share_join. auto. Qed.

Lemma data_at_share_join{cs: compspecs}:
  forall sh1 sh2 sh t v p,
    sepalg.join sh1 sh2 sh ->
   data_at sh1 t v p * data_at sh2 t v p = data_at sh t v p.
Proof. intros. apply field_at_share_join; auto. Qed.

Lemma data_at__share_join{cs: compspecs}:
  forall sh1 sh2 sh t p,
    sepalg.join sh1 sh2 sh ->
   data_at_ sh1 t p * data_at_ sh2 t p = data_at_ sh t p.
Proof. intros. apply data_at_share_join; auto. Qed.

Lemma nonreadable_memory_block_field_at:
  forall  {cs: compspecs}
      sh t gfs v p,
  ~ readable_share sh ->
   value_fits _ v ->
   memory_block sh (sizeof (nested_field_type t gfs)) (field_address t gfs p) = field_at sh t gfs v p.
Proof.
  intros until p. intros NONREAD VF.
  unfold field_address.
  destruct (field_compatible_dec t gfs p).
  + unfold field_at_, field_at.
    rewrite prop_true_andp by auto.
    assert (isptr p) by auto; destruct p; try contradiction; clear H.
    inv_int i.
    unfold at_offset, offset_val.
    solve_mod_modulus.
    pose proof field_compatible_nested_field _ _ _ f.
    revert H f;
    unfold field_compatible;
    unfold size_compatible, align_compatible, offset_val;
    solve_mod_modulus;
    intros.
    pose proof nested_field_offset_in_range t gfs.
    spec H1; [tauto |].
    spec H1; [tauto |].
    rewrite (Z.mod_small ofs) in * by omega.
    pose proof Zmod_le (ofs + nested_field_offset t gfs) Ptrofs.modulus.
    spec H2; [pose proof Ptrofs.modulus_pos; omega |].
    revert H; solve_mod_modulus; intros.
    rewrite Zmod_small in H by (pose proof sizeof_pos (nested_field_type t gfs); omega).
    apply nonreadable_memory_block_data_at_rec; try tauto; try omega.
  + unfold field_at_, field_at.
    rewrite memory_block_isptr.
    apply pred_ext; normalize.
Qed.

Lemma nonreadable_memory_block_data_at: forall  {cs: compspecs} sh t v p,
  ~ readable_share sh ->
  field_compatible t nil p ->
  value_fits t v ->
  memory_block sh (sizeof t) p = data_at sh t v p.
Proof.
  intros.
  replace p with (field_address t nil p) at 1.
  change t with (nested_field_type t nil) at 1.
  apply nonreadable_memory_block_field_at; auto.
  rewrite field_compatible_field_address by auto.
  simpl.
  change (nested_field_offset t nil) with 0.
  apply isptr_offset_val_zero.
  auto with field_compatible.
Qed.

Lemma nonreadable_field_at_eq {cs: compspecs} :
  forall sh t gfs v v' p,
   ~ readable_share sh ->
   (value_fits (nested_field_type t gfs) v <-> value_fits (nested_field_type t gfs) v') ->
   field_at sh t gfs v p = field_at sh t gfs v' p.
Proof.
intros.
rewrite !field_at_data_at.
apply pred_ext; saturate_local.
rewrite <- !nonreadable_memory_block_data_at; auto.
apply H0; auto.
destruct (readable_share_dec sh); try contradiction.
rewrite <- !nonreadable_memory_block_data_at; auto.
apply H0; auto.
Qed.

Lemma nonreadable_readable_memory_block_data_at_join
    {cs: compspecs}:
  forall ash bsh psh t v p,
    sepalg.join ash bsh psh ->
    ~ readable_share ash ->
   memory_block ash (sizeof t) p * data_at bsh t v p = data_at psh t v p.
Proof.
intros.
apply pred_ext; saturate_local.
rewrite nonreadable_memory_block_data_at with (v0:=v); auto.
unfold data_at.
erewrite field_at_share_join; eauto. apply derives_refl.
rewrite nonreadable_memory_block_data_at with (v0:=v); auto.
unfold data_at.
erewrite field_at_share_join; eauto.
apply derives_refl.
Qed.
(*
Lemma nonreadable_data_at_rec_eq {cs: compspecs} :
  forall sh t v v' p,
    ~readable_share sh ->
    field_compatible t nil p ->
     data_at_rec sh t v p = data_at_rec sh t v' p.
Proof.
  intros.
  rewrite <- !(nonreadable_memory_block_data_at_rec); auto.
Qed.
*)
Lemma nonreadable_data_at_eq {cs: compspecs}:
  forall sh t v v' p, ~readable_share sh ->
   (value_fits t v <-> value_fits t v') ->
     data_at sh t v p = data_at sh t v' p.
Proof.
intros.
unfold data_at.
apply nonreadable_field_at_eq; auto.
Qed.

Lemma field_at_share_join_W {cs: compspecs}:
  forall sh1 sh2 sh t gfs v1 v2 p,
    sepalg.join sh1 sh2 sh ->
    writable_share sh1 ->
    field_at sh1 t gfs v1 p * field_at sh2 t gfs v2 p |-- field_at sh t gfs v1 p.
Proof.
  intros.
  pose proof join_writable_readable H H0.
  rewrite (add_andp _ _ (field_at_local_facts sh1 _ _ _ _)).
  rewrite (add_andp _ _ (field_at_local_facts sh2 _ _ _ _)).
  normalize.
  rewrite (nonreadable_field_at_eq sh2 _ _ v2 v1) by (auto; tauto).
  erewrite field_at_share_join by eauto.
  auto.
Qed.

Lemma data_at_share_join_W {cs: compspecs}:
  forall sh1 sh2 sh t v1 v2 p,
    sepalg.join sh1 sh2 sh ->
    writable_share sh1 ->
    data_at sh1 t v1 p * data_at sh2 t v2 p |-- data_at sh t v1 p.
Proof.
  intros.
  apply field_at_share_join_W; auto.
Qed.

Lemma value_fits_Tint_trivial {cs: compspecs} :
  forall s a  i, value_fits (Tint I32 s a) (Vint i).
Proof.
intros.
rewrite value_fits_eq; simpl.
destruct (attr_volatile a); auto.
hnf. intro. apply Coq.Init.Logic.I.
Qed.

(* TODO: move all change type lemmas into one file. Also those change compspecs lemmas. *)
Lemma data_at_tuint_tint {cs: compspecs}: forall sh v p, data_at sh tuint v p = data_at sh tint v p.
Proof.
  intros.
  unfold data_at, field_at.
  f_equal.
  unfold field_compatible.
  apply ND_prop_ext.
  assert (align_compatible tuint p <-> align_compatible tint p); [| tauto].
  destruct p; simpl; try tauto.
  split; intros.
  + eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
    eapply align_compatible_rec_by_value; [reflexivity |].
    auto.
  + eapply align_compatible_rec_by_value_inv in H; [| reflexivity].
    eapply align_compatible_rec_by_value; [reflexivity |].
    auto.
Qed.

Lemma mapsto_field_at {cs: compspecs} sh t gfs v v' p:
  type_is_by_value (nested_field_type t gfs) = true ->
  type_is_volatile (nested_field_type t gfs) = false ->
  field_compatible t gfs p ->
  JMeq v v' ->
  mapsto sh (nested_field_type t gfs) (field_address t gfs p) v = field_at sh t gfs v' p.
Proof.
  intros.
  unfold field_at, at_offset.
  rewrite by_value_data_at_rec_nonvolatile by auto.
  apply (fun HH => JMeq_trans HH (JMeq_sym (repinject_JMeq _ v' H))) in H2.
  apply JMeq_eq in H2.
  rewrite prop_true_andp by auto.
  f_equal; auto.
  apply field_compatible_field_address; auto.
Qed.

Lemma mapsto_field_at_ramify {cs: compspecs} sh t gfs v v' w w' p:
  type_is_by_value (nested_field_type t gfs) = true ->
  type_is_volatile (nested_field_type t gfs) = false ->
  JMeq v v' ->
  JMeq w w' ->
  field_at sh t gfs v' p |--
    mapsto sh (nested_field_type t gfs) (field_address t gfs p) v *
     (mapsto sh (nested_field_type t gfs) (field_address t gfs p) w -*
        field_at sh t gfs w' p).
Proof.
  intros.
  unfold field_at, at_offset.
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply (fun HH => JMeq_trans HH (JMeq_sym (repinject_JMeq _ v' H))) in H1; apply JMeq_eq in H1.
  apply (fun HH => JMeq_trans HH (JMeq_sym (repinject_JMeq _ w' H))) in H2; apply JMeq_eq in H2.
  normalize.
  rewrite field_compatible_field_address by auto.
  subst.
  apply RAMIF_PLAIN.solve with emp; [rewrite sepcon_emp | rewrite emp_sepcon]; auto.
Qed.

Lemma mapsto_data_at {cs: compspecs} sh t v v' p :  (* not needed here *)
  type_is_by_value t = true ->
  type_is_volatile t = false ->
  isptr p ->
  size_compatible t p ->
  align_compatible t p ->
  complete_legal_cosu_type t = true ->
  JMeq v v' ->
  mapsto sh t p v = data_at sh t v' p.
Proof.
  intros.
  unfold data_at, field_at, at_offset, offset_val.
  simpl.
  destruct p; inv H1.
  rewrite ptrofs_add_repr_0_r.
  rewrite by_value_data_at_rec_nonvolatile by auto.
  apply (fun HH => JMeq_trans HH (JMeq_sym (repinject_JMeq _ v' H))) in H5; apply JMeq_eq in H5.
  rewrite prop_true_andp; auto.
  f_equal. auto.
  repeat split; auto.
Qed.

Lemma mapsto_data_at' {cs: compspecs} sh t v v' p:
  type_is_by_value t = true ->
  type_is_volatile t = false ->
  field_compatible t nil p ->
  JMeq v v' ->
  mapsto sh t p v = data_at sh t v' p.
Proof.
  intros.
  unfold data_at, field_at, at_offset, offset_val.
  simpl.
  rewrite prop_true_andp by auto.
  rewrite by_value_data_at_rec_nonvolatile by auto.
  apply (fun HH => JMeq_trans HH (JMeq_sym (repinject_JMeq _ v' H))) in H2; apply JMeq_eq in H2.
  f_equal; auto.
  destruct H1. destruct p; try contradiction.
  rewrite ptrofs_add_repr_0_r. auto.
Qed.

Lemma headptr_field_compatible: forall {cs: compspecs} t path p, 
   headptr p ->
   complete_legal_cosu_type t = true ->
   legal_nested_field t path ->
   sizeof t < Ptrofs.modulus ->
   align_compatible_rec cenv_cs t 0 ->
   field_compatible t path p.
Proof.
 intros.
 destruct H as [b ?]; subst p.
 repeat split; auto.
Qed.

(*
Lemma headptr_field_compatible' {cs: compspecs}: forall t p,
  headptr p ->
  legal_alignas_type t = true ->
  legal_cosu_type t = true ->
  sizeof t < Ptrofs.modulus ->
  complete_type cenv_cs t = true ->
  field_compatible t nil p.
Proof.
  intros.
  split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]].
  + apply headptr_isptr; auto.
  + auto.
  + auto.
  + auto.
  + auto.
  + destruct H as [b ?]; subst.
    simpl.
    change (Ptrofs.unsigned Ptrofs.zero) with 0.
    omega.
  + destruct H as [b ?]; subst.
    simpl.
    change (Ptrofs.unsigned Ptrofs.zero) with 0.
    apply Z.divide_0_r.
  + simpl.
    auto.
Qed.
*)

Lemma mapsto_data_at'' {cs: compspecs}: forall sh t v v' p,
  ((type_is_by_value t) && (complete_legal_cosu_type t) && (negb (type_is_volatile t)) && is_aligned cenv_cs ha_env_cs la_env_cs t 0 = true)%bool ->
  headptr p ->
  JMeq v v' ->
  mapsto sh t p v = data_at sh t v' p.
Proof.
  intros.
  rewrite !andb_true_iff in H.
  destruct H as [[[? ?] ?] ?].
  rewrite negb_true_iff in H3.
  apply mapsto_data_at'; auto.
  apply headptr_field_compatible; auto.
  + destruct t; inv H; simpl; auto.
  + destruct t as [| [ |  |  | ] ? | | [ | ] | | | | |]; inv H; reflexivity.
  + apply la_env_cs_sound in H4; auto.
Qed.

Lemma data_at_type_changable {cs}: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  @data_at cs sh t1 v1 = data_at sh t2 v2.
Proof. intros. subst. apply JMeq_eq in H0. subst v2. reflexivity. Qed.

Lemma field_at_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) gfs v1 v2,
  JMeq v1 v2 ->
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @field_at cs_from sh t gfs v1 = @field_at cs_to sh t gfs v2.
Proof.
  intros.
  unfold field_at.
  extensionality p.
  apply andp_prop_ext.
  + apply field_compatible_change_composite; auto.
  + intros.
    pose proof H1.
    rewrite field_compatible_change_composite in H2 by auto.
    f_equal.
    - revert v1 H;
      rewrite nested_field_type_change_composite by auto.
      intros.
      apply data_at_rec_change_composite; auto.
      apply nested_field_type_preserves_change_composite; auto.
    - apply nested_field_offset_change_composite; auto.
Qed.

Lemma field_at__change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) gfs,
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @field_at_ cs_from sh t gfs = @field_at_ cs_to sh t gfs.
Proof.
  intros.
  apply field_at_change_composite; auto.
  rewrite nested_field_type_change_composite by auto.
  apply default_val_change_composite.
  apply nested_field_type_preserves_change_composite; auto.
Qed.

Lemma data_at_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) v1 v2,
  JMeq v1 v2 ->
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @data_at cs_from sh t v1 = @data_at cs_to sh t v2.
Proof.
  intros.
  apply field_at_change_composite; auto.
Qed.

Lemma data_at__change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type),
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  @data_at_ cs_from sh t = @data_at_ cs_to sh t.
Proof.
  intros.
  apply field_at__change_composite; auto.
Qed.

(* TODO: rename and clean up all array_at_data_at lemmas. *)
Lemma array_at_data_at1 {cs} : forall sh t gfs lo hi v p,
   lo <= hi ->
   field_compatible0 t (gfs SUB lo) p ->
   field_compatible0 t (gfs SUB hi) p ->
  @array_at cs sh t gfs lo hi v p =
  at_offset (@data_at cs sh (nested_field_array_type t gfs lo hi) v)
               (nested_field_offset t (ArraySubsc lo :: gfs)) p.
Proof.
  intros. rewrite array_at_data_at by auto. unfold at_offset. apply pred_ext; normalize.
Qed.

Lemma data_at_ext_derives {cs} sh t v v' p q: v=v' -> p=q -> @data_at cs sh t v p |-- @data_at cs sh t v' q.
Proof. intros; subst. 
apply derives_refl.
Qed.

Lemma data_at_ext_eq {cs} sh t v v' p q: v=v' -> p=q -> @data_at cs sh t v p = @data_at cs sh t v' q.
Proof. intros; subst. trivial. Qed.

(* does not simplify array indices, because that might be too expensive *)
Ltac simpl_compute_legal_nested_field :=
  repeat match goal with
  | |- context [ compute_legal_nested_field ?T ?L ] =>
    let r := eval hnf in (compute_legal_nested_field T L) in
    change (compute_legal_nested_field T L) with r
  end.

Ltac solve_legal_nested_field_in_entailment :=
   match goal with
   | |- _ |-- !! legal_nested_field ?t_root ?gfs =>
     try unfold t_root;
     try unfold gfs;
     try match gfs with
     | (?gfs1 ++ ?gfs0) => try unfold gfs1; try unfold gfs0
     end
  end;
  first
  [ apply prop_right; apply compute_legal_nested_field_spec';
    simpl_compute_legal_nested_field;
    repeat constructor; omega
  |
  apply compute_legal_nested_field_spec;
  simpl_compute_legal_nested_field;
  repeat constructor;
  try solve [apply prop_right; auto; omega];
  try solve [normalize; apply prop_right; auto; omega]
  ].

Ltac headptr_field_compatible :=
  match goal with H: headptr ?P |- field_compatible _ _ ?P =>
  apply headptr_field_compatible;
        [ apply H | reflexivity | | simpl; computable | apply la_env_cs_sound; reflexivity];
    apply compute_legal_nested_field_spec';
    simpl_compute_legal_nested_field;
    repeat apply Forall_cons; try apply Forall_nil
  end.

Hint Extern 2 (field_compatible _ _ _) => headptr_field_compatible : field_compatible.

(* BEGIN New experiments *)

Lemma data_at_data_at_cancel  {cs: compspecs}: forall sh t v v' p,
  v = v' ->
  data_at sh t v p |-- data_at sh t v' p.
Proof. intros. subst. apply derives_refl. Qed.
 
Hint Resolve data_at_data_at_cancel : cancel.


Lemma field_at_field_at_cancel  {cs: compspecs}: forall sh t gfs v v' p,
  v = v' ->
  field_at sh t gfs v p |-- field_at sh t gfs v' p.
Proof. intros. subst. apply derives_refl. Qed.
 
Hint Resolve data_at_data_at_cancel : cancel.
Hint Resolve field_at_field_at_cancel : cancel.

Lemma data_at__data_at {cs: compspecs}:
   forall sh t v p, v = default_val t -> data_at_ sh t p |-- data_at sh t v p.
Proof.
intros; subst; unfold data_at_; apply derives_refl.
Qed.

Lemma field_at__field_at {cs: compspecs} :
   forall sh t gfs v p, v = default_val (nested_field_type t gfs) -> field_at_ sh t gfs p |-- field_at sh t gfs v p.
Proof.
intros; subst; unfold field_at_; apply derives_refl.
Qed.

Lemma data_at__field_at {cs: compspecs}:
   forall sh t v p, v = default_val t -> data_at_ sh t p |-- field_at sh t nil v p.
Proof.
intros; subst; unfold data_at_; apply derives_refl.
Qed.

Lemma field_at__data_at {cs: compspecs} :
   forall sh t v p, v = default_val (nested_field_type t nil) -> field_at_ sh t nil p |-- data_at sh t v p.
Proof.
intros; subst; unfold field_at_; apply derives_refl.
Qed.


Hint Resolve data_at__data_at : cancel.
Hint Resolve field_at__field_at : cancel.
Hint Resolve data_at__field_at : cancel.
Hint Resolve field_at__data_at : cancel.

Hint Extern 1 (_ = @default_val _ _) =>
 match goal with |- ?A = ?B => 
     let x := fresh "x" in set (x := B); hnf in x; subst x;
     match goal with |- ?A = ?B => constr_eq A B; reflexivity
  end end.

Hint Extern 1 (_ = _) => 
  match goal with |- ?A = ?B => constr_eq A B; reflexivity end : cancel.

(* END new experiments *)


Lemma data_at__Tarray:
  forall {CS: compspecs} sh t n a,
  data_at_ sh (Tarray t n a) = 
  data_at sh (Tarray t n a) (list_repeat (Z.to_nat n) (default_val t)).
Proof.
intros.
unfold data_at_, field_at_, data_at.
extensionality p.
simpl.
f_equal.
Qed.

Lemma data_at__tarray:
  forall {CS: compspecs} sh t n,
  data_at_ sh (tarray t n) = 
  data_at sh (tarray t n) (list_repeat (Z.to_nat n) (default_val t)).
Proof. intros; apply data_at__Tarray; auto. Qed.

Lemma data_at__Tarray':
  forall {CS: compspecs} sh t n a v, 
  v = list_repeat (Z.to_nat n) (default_val t) ->
  data_at_ sh (Tarray t n a) = data_at sh (Tarray t n a) v.
Proof.
intros.
unfold data_at_, field_at_, data_at.
extensionality p.
simpl.
f_equal.
subst.
reflexivity.
Qed.

Lemma data_at__tarray':
  forall {CS: compspecs} sh t n v, 
  v = list_repeat (Z.to_nat n) (default_val t) ->
  data_at_ sh (tarray t n) = data_at sh (tarray t n) v.
Proof. intros; apply data_at__Tarray'; auto. Qed.

Ltac unfold_data_at_ p :=
 match goal with |- context [data_at_ ?sh ?t p] =>
  let d := fresh "d" in set (d := data_at_ sh t p);
  pattern d;
  let g := fresh "goal" in
   match goal with |- ?G d => set (g:=G) end;
  revert d;
  match t with
   | Tarray ?t1 ?n _ => 
          erewrite data_at__Tarray' by apply eq_refl;
          try change (default_val t1) with Vundef
   | tarray ?t1 ?n => 
          erewrite data_at__tarray' by apply eq_refl;
          try change (default_val t1) with Vundef
   | _ => change (data_at_ sh t p) with (data_at sh t (default_val t) p);
              try change (default_val t) with Vundef
  end;
  subst g; intro d; subst d; cbv beta
 end.

Lemma change_compspecs_field_at_cancel:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type) gfs
        (v1: @reptype cs1 (@nested_field_type cs1 t1 gfs))
        (v2: @reptype cs2 (@nested_field_type cs2 t2 gfs))
        (p: val),
    t1 = t2 -> 
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   JMeq v1 v2 -> 
   @field_at cs1 sh t1 gfs v1 p |-- @field_at cs2 sh t2 gfs v2 p.
Proof.
intros.
subst t2.
apply derives_refl'.
apply equal_f.
apply @field_at_change_composite with CCE; auto.
Qed.

Lemma change_compspecs_data_at_cancel:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type)
        (v1: @reptype cs1 t1) (v2: @reptype cs2 t2)
        (p: val),
    t1 = t2 -> 
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   JMeq v1 v2 -> 
   @data_at cs1 sh t1 v1 p |-- @data_at cs2 sh t2 v2 p.
Proof.
intros.
apply change_compspecs_field_at_cancel; auto.
Qed.

Lemma change_compspecs_field_at_cancel2:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type) gfs
        (p: val),
    t1 = t2 -> 
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   @field_at_ cs1 sh t1 gfs p |-- @field_at_ cs2 sh t2 gfs p.
Proof.
intros.
subst t2.
apply @change_compspecs_field_at_cancel with CCE; auto.
pose proof (@nested_field_type_change_composite cs1 cs2 CCE t1 H0 gfs).
rewrite H.
apply @default_val_change_composite with CCE; auto.
apply nested_field_type_preserves_change_composite; auto.
Qed.

Lemma change_compspecs_data_at_cancel2:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type)
        (p: val),
    t1 = t2 -> 
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   @data_at_ cs1 sh t1 p |-- @data_at_ cs2 sh t2 p.
Proof.
intros.
apply change_compspecs_field_at_cancel2; auto.
Qed.

Lemma change_compspecs_field_at_cancel3:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type) gfs
        (v1: @reptype cs1 (@nested_field_type cs1 t1 gfs))
        (p: val),
    t1 = t2 -> 
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   @field_at cs1 sh t1 gfs v1 p |-- @field_at_ cs2 sh t2 gfs p.
Proof.
intros.
subst t2.
apply derives_trans with (@field_at_ cs1 sh t1 gfs p).
apply field_at_field_at_.
apply @change_compspecs_field_at_cancel2 with CCE; auto.
Qed.

Lemma change_compspecs_data_at_cancel3:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type)
        (v1: @reptype cs1 t1)
        (p: val),
    t1 = t2 -> 
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   @data_at cs1 sh t1 v1 p |-- @data_at_ cs2 sh t2 p.
Proof.
intros.
apply @change_compspecs_field_at_cancel3 with CCE; auto.
Qed.

Hint Extern 2 (@data_at_ ?cs1 ?sh _ ?p |-- @data_at_ ?cs2 ?sh _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_data_at_cancel2; reflexivity) : cancel.

Hint Extern 2 (@data_at ?cs1 ?sh _ _ ?p |-- @data_at_ ?cs2 ?sh _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_data_at_cancel3; reflexivity) : cancel.

Hint Extern 2 (@data_at ?cs1 ?sh _ _ ?p |-- @data_at ?cs2 ?sh _ _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_data_at_cancel; 
       [ reflexivity | reflexivity | apply JMeq_refl]) : cancel.

Hint Extern 2 (@field_at_ ?cs1 ?sh _ ?gfs ?p |-- @field_at_ ?cs2 ?sh _ ?gfs ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_field_at_cancel2; reflexivity) : cancel.

Hint Extern 2 (@field_at ?cs1 ?sh _ ?gfs _ ?p |-- @field_at_ ?cs2 ?sh _ ?gfs ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_field_at_cancel3; reflexivity) : cancel.

Hint Extern 2 (@field_at ?cs1 ?sh _ ?gfs _ ?p |-- @field_at ?cs2 ?sh _ ?gfs _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_field_at_cancel; 
        [ reflexivity | reflexivity | apply JMeq_refl]) : cancel.

