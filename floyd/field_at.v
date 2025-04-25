Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.zlist.sublist.
Require Import VST.floyd.local2ptree_typecheck.
Import LiftNotation.

Local Unset SsrRewrite.

(************************************************

Definition of nested_reptype_structlist, field_at, array_at, data_at, nested_sfieldlist_at

************************************************)

Section CENV.

Context `{!VSTGS OK_ty Σ} {cs: compspecs}.

Lemma struct_Prop_cons2:
  forall it it' m (A: member -> Type)
   (P: forall it, A it -> Prop)
   (v: compact_prod (map A (it::it'::m))),
 struct_Prop (it :: it' :: m) P v =
    (P _ (fst v) /\ struct_Prop (it'::m) P (snd v)).
Proof.
intros.
destruct v.
reflexivity.
Qed.

Lemma struct_Prop_ext_derives: forall m {A0 A1} (P0: forall it, A0 it -> Prop) (P1: forall it, A1 it -> Prop) v0 v1,
  members_no_replicate m = true ->
  (forall i d0 d1, in_members i m ->
     P0 _ (proj_struct i m v0 d0) -> P1 _ (proj_struct i m v1 d1)) ->
  struct_Prop m P0 v0 -> struct_Prop m P1 v1.
Proof.
  intros. revert H1.
  destruct m as [| a0 m]; [simpl; auto |].
  revert a0 v0 v1 H H0; induction m as [| a1 m]; intros.
  + specialize (H0 (name_member a0)).
    simpl in H0.
    unfold field_type, Ctypes.field_type in H0.
    simpl in H0.
    rewrite if_true in H0 by auto.
    specialize (H0 v0 v1).
    spec H0; [left; reflexivity |].
    destruct (member_dec a0 a0); [ | congruence].
    unfold eq_rect_r in H0; rewrite <- !eq_rect_eq in H0.
    simpl. auto.
  + revert H1.
    change (struct_Prop (a0 :: a1 :: m) P0 v0) with
      (P0 a0 (fst v0) /\ struct_Prop (a1 :: m) P0 (snd v0)).
    change (struct_Prop (a0 :: a1 :: m) P1 v1) with
      (P1 a0 (fst v1) /\ struct_Prop (a1 :: m) P1 (snd v1)).
     intro.
      rewrite fieldlist.members_no_replicate_ind in H.
      destruct H as [H H'].
       specialize (IHm a1 (snd v0) (snd v1) H').
      split.
    - destruct H1 as [H1 _]; revert H1.
      specialize (H0 (name_member a0)).
      unfold proj_struct in H0.
      revert H0; unfold field_type; simpl.
      rewrite if_true by auto.
    destruct (member_dec a0 a0); [ | congruence].
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      intros. apply (H0 (fst v0) (fst v1)); auto.
      hnf. left; reflexivity.
    - destruct H1 as [_ H1]; revert H1.
      apply IHm; clear IHm.
      assert (name_member a0 <> name_member a1) by (contradict H; left; auto).
      intros.
      specialize (H0 i).
      assert (i<> name_member a0). contradict H1. subst i. contradiction.
      clear H H'.
      assert (get_member i (a0::a1::m) = get_member i (a1::m))
         by (simpl; rewrite if_false; auto).
      unfold proj_struct in *.
      rewrite H in H0.
      specialize (H0 d0 d1).
      spec H0; [unfold in_members; right; auto | ].
      assert (proj_compact_prod (get_member i (a1 :: m))
                  (a0 :: a1 :: m) v0 d0 member_dec =
                proj_compact_prod (get_member i (a1:: m)) (a1 :: m)
                 (snd v0) d0 member_dec).
         clear - H1 H4.
         unfold proj_compact_prod. unfold list_rect; cbv beta iota.
         destruct (member_dec (get_member i (a1 :: m)) a0).
         exfalso. subst a0. rewrite name_member_get in H1, H4. contradiction.
         reflexivity.
      rewrite H5 in H0; clear H5.
      assert (proj_compact_prod (get_member i (a1 :: m))
                  (a0 :: a1 :: m) v1 d1 member_dec =
                proj_compact_prod (get_member i (a1 :: m)) (a1 :: m)
                 (snd v1) d1 member_dec).
         clear - H1 H4.
         unfold proj_compact_prod. unfold list_rect; cbv beta iota.
         destruct (member_dec (get_member i (a1 :: m)) a0).
         exfalso. subst a0. rewrite name_member_get in H1, H4. contradiction.
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
 ⌜field_compatible t gfs p⌝ ∧
 at_offset (data_at_rec sh (nested_field_type t gfs) v) (nested_field_offset t gfs) p.
Arguments field_at sh t gfs v p : simpl never.
Global Typeclasses Opaque field_at.

Definition field_at_ (sh: Share.t) (t: type) (gfs: list gfield) (p: val): mpred :=
  field_at sh t gfs (default_val (nested_field_type t gfs)) p.

Arguments field_at_ sh t gfs p : simpl never.

Definition data_at (sh: Share.t) (t: type) (v: reptype t) := field_at sh t nil v.
Global Typeclasses Opaque data_at.

Definition data_at_ (sh: Share.t) (t: type) := field_at_ sh t nil.

Definition nested_reptype_structlist t gfs (m: members) :=
  compact_prod (map (fun it => reptype (nested_field_type t (StructField (name_member it) :: gfs))) m).

Definition nested_reptype_unionlist t gfs (m: members) :=
  compact_sum (map (fun it => reptype (nested_field_type t (UnionField (name_member it) :: gfs))) m).

Lemma map_members_ext: forall A (f f':member -> A) (m: list member),
  members_no_replicate m = true ->
  (forall i, in_members i m -> f (get_member i m) = f' (get_member i m)) ->
  map f m = map f' m.
Proof.
  intros.
  induction m as [| a0 m].
  + reflexivity.
  + simpl.
    rewrite members_no_replicate_ind in H.
    f_equal.
    - specialize (H0 (name_member a0)).
      unfold field_type, in_members in H0.
      simpl in H0; if_tac in H0; [| congruence].
      apply H0; auto.
    - apply IHm. tauto.
      intros.
      specialize (H0 i).
      unfold in_members in H0.
      simpl in H0; if_tac in H0; [subst; tauto |].
      apply H0; auto.
Defined.

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
  | nil => ⌜field_compatible t gfs p⌝ ∧ emp
  | _ => struct_pred m (fun it v p =>
           withspacer sh
            (nested_field_offset t gfs +
              (field_offset cenv_cs (name_member it) m + sizeof (field_type (name_member it) m)))
            (nested_field_offset t gfs +
              field_offset_next cenv_cs (name_member it) m (sizeof (nested_field_type t gfs)))
            (field_at sh t (StructField (name_member it) :: gfs) v) p) v p
  end.

Definition nested_ufieldlist_at sh t gfs m (v: nested_reptype_unionlist t gfs m) (p: val): mpred :=
  match m with
  | nil => ⌜field_compatible t gfs p⌝ ∧ emp
  | _ => union_pred m (fun it v p =>
           withspacer sh
            (nested_field_offset t gfs + sizeof (field_type (name_member it) m))
            (nested_field_offset t gfs + sizeof (nested_field_type t gfs))
            (field_at sh t (UnionField (name_member it) :: gfs) v) p) v p
  end.

Definition array_at (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z)
  (v: list (reptype (nested_field_type t (ArraySubsc 0 :: gfs)))) (p: val) : mpred :=
  ⌜field_compatible0 t (ArraySubsc lo :: gfs) p /\
   field_compatible0 t (ArraySubsc hi :: gfs) p⌝ ∧
  array_pred lo hi
    (fun i v => at_offset (data_at_rec sh (nested_field_type t (ArraySubsc 0 :: gfs)) v)
       (nested_field_offset t (ArraySubsc i :: gfs))) v p.

Definition array_at_ (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z) : val -> mpred :=
 array_at sh t gfs lo hi (Zrepeat (default_val _) (hi-lo)).

(************************************************

field_compatible, local_facts, isptr and offset_zero properties

************************************************)

Lemma field_at_local_facts:
  forall sh t path v c,
     field_at sh t path v c ⊢ ⌜field_compatible t path c /\ value_fits (nested_field_type t path) v⌝.
Proof.
  intros.
  unfold field_at, at_offset.
  rewrite data_at_rec_value_fits.
  by iIntros "(% & %)"; iPureIntro.
Qed.

Lemma field_at_compatible':
 forall sh t path v c,
     field_at sh t path v c =
     (⌜field_compatible t path c⌝ ∧ field_at sh t path v c).
Proof.
intros.
unfold field_at; normalize.
f_equal; f_equal; apply prop_ext; tauto.
Qed.

Lemma field_at__local_facts: forall sh t gfs p,
  field_at_ sh t gfs p ⊢ ⌜field_compatible t gfs p⌝.
Proof.
  intros.
  unfold field_at_, field_at.
  normalize.
Qed.

Lemma data_at_local_facts:
   forall sh t v p, data_at sh t v p ⊢ ⌜field_compatible t nil p /\ value_fits t v⌝.
Proof. intros. apply field_at_local_facts. Qed.

Lemma data_at__local_facts: forall sh t p, data_at_ sh t p ⊢ ⌜field_compatible t nil p⌝.
Proof. intros.
  apply field_at__local_facts.
Qed.

Lemma array_at_local_facts: forall sh t gfs lo hi v p,
  array_at sh t gfs lo hi v p ⊢
    ⌜field_compatible0 t (ArraySubsc lo :: gfs) p
        /\ field_compatible0 t (ArraySubsc hi :: gfs) p
        /\ Zlength v = hi - lo
        /\ Forall (value_fits (nested_field_type t (ArraySubsc 0 :: gfs))) v⌝.
Proof.
  intros.
  unfold array_at.
  rewrite array_pred_local_facts.
  2: { intros.
       unfold at_offset.
       apply data_at_rec_value_fits. }
  normalize.
Qed.

Lemma array_at__local_facts: forall sh t gfs lo hi p,
  array_at_ sh t gfs lo hi p ⊢
    ⌜field_compatible0 t (ArraySubsc lo :: gfs) p
        /\ field_compatible0 t (ArraySubsc hi :: gfs) p⌝.
Proof.
  intros.
  unfold array_at_.
  rewrite array_at_local_facts; eauto.
  apply bi.pure_mono; intuition.
Qed.

Lemma field_at_isptr: forall sh t gfs v p,
  field_at sh t gfs v p = (⌜isptr p⌝ ∧ field_at sh t gfs v p).
Proof.
  intros. unfold field_at.
  normalize.
  do 2 f_equal; apply prop_ext; split; last tauto.
  intros (? & ?); split3; auto.
Qed.

Lemma field_at_offset_zero: forall sh t gfs v p,
  field_at sh t gfs v p = field_at sh t gfs v (offset_val 0 p).
Proof.
  intros. unfold field_at.
  destruct p; try done; simpl.
  rewrite Ptrofs.add_zero; auto.
Qed.

Lemma field_at__isptr: forall sh t gfs p,
  field_at_ sh t gfs p = (⌜isptr p⌝ ∧ field_at_ sh t gfs p).
Proof. intros; apply field_at_isptr. Qed.

Lemma field_at__offset_zero: forall sh t gfs p,
  field_at_ sh t gfs p = field_at_ sh t gfs (offset_val 0 p).
Proof. intros; apply field_at_offset_zero. Qed.

Lemma data_at_isptr: forall sh t v p, data_at sh t v p = (⌜isptr p⌝ ∧ data_at sh t v p).
Proof. intros; apply field_at_isptr. Qed.

Lemma data_at_offset_zero: forall sh t v p, data_at sh t v p = data_at sh t v (offset_val 0 p).
Proof. intros; apply field_at_offset_zero. Qed.

Lemma data_at__isptr: forall sh t p, data_at_ sh t p = (⌜isptr p⌝ ∧ data_at_ sh t p).
Proof. intros; apply data_at_isptr. Qed.

Lemma data_at__offset_zero: forall sh t p, data_at_ sh t p = data_at_ sh t (offset_val 0 p).
Proof. intros; apply field_at__offset_zero. Qed.

(************************************************

Ext lemmas of array_at

************************************************)

Lemma array_at_ext_derives: forall sh t gfs lo hi v0 v1 p,
  Zlength v0 = Zlength v1 ->
  (forall i u0 u1,
     lo <= i < hi ->
     JMeq u0 (Znth (i-lo) v0) ->
     JMeq u1 (Znth (i-lo) v1) ->
     field_at sh t (ArraySubsc i :: gfs) u0 p ⊢
     field_at sh t (ArraySubsc i :: gfs) u1 p) ->
  array_at sh t gfs lo hi v0 p ⊢ array_at sh t gfs lo hi v1 p.
Proof.
  intros until p. intro ZL; intros.
  unfold array_at, field_at.
  normalize.
  eapply array_pred_ext_derives.
  1: intro; lia.
  intros.
  specialize (H i).
  clear ZL.
  revert v0 v1 H.
  unfold field_at.
  rewrite @nested_field_type_ArraySubsc with (i := i).
  intros.
  specialize (H (Znth (i - lo) v0) (Znth (i - lo) v1)).
  do 3 (spec H; [auto |]).
  rewrite !prop_true_andp in H by (apply (field_compatible_range _ lo hi); auto).
  auto.
Qed.

Lemma andp_prop_eq : forall P P' (Q Q' : mpred) (Hdec : {P} + {~P} ),
  (P <-> P') -> (P -> Q = Q') -> (⌜P⌝ ∧ Q) = (⌜P'⌝ ∧ Q').
Proof.
  intros.
  destruct Hdec; [rewrite !prop_true_andp by tauto | rewrite !prop_false_andp by tauto]; auto.
Qed.

Lemma andp_prop_eq1 : forall P (Q Q' : mpred) (Hdec : {P} + {~P} ), (P -> Q = Q') ->
  (⌜P⌝ ∧ Q) = (⌜P⌝ ∧ Q').
Proof.
  intros; apply andp_prop_eq; auto.
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
  unfold array_at.
  apply andp_prop_eq1.
  { destruct (field_compatible0_dec t (gfs SUB lo) p); [|right; tauto].
    destruct (field_compatible0_dec t (gfs SUB hi) p); [left | right]; tauto. }
  intros (? & ?).
  apply aggregate_pred.array_pred_eq; auto.
  intros.
  specialize (H0 i).
  unfold field_at in H0.
  rewrite @nested_field_type_ArraySubsc with (i := i) in H0.
  assert (field_compatible t (gfs SUB i) p) as Hcompat by (eapply (field_compatible_range _ lo hi); eauto).
  setoid_rewrite <- (prop_true_andp _ _ Hcompat); auto.
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
  apply andp_prop_eq.
  { apply field_compatible_dec. }
  + rewrite !field_compatible0_cons, H0.
    assert (0 <= 0 <= n) by lia.
    assert (0 <= n <= n) by lia.
    tauto.
  + intros.
    apply (JMeq_trans (unfold_reptype_JMeq _ v1)) in H2.
    forget (unfold_reptype v1) as v1'.
    clear v1.
    cbv iota beta in v1'.
    apply JMeq_eq in H2.
    rewrite Z.max_r by lia.
    apply aggregate_pred.array_pred_eq.
    - subst; auto.
    - intros.
      rewrite at_offset_eq.
      rewrite <- at_offset_eq2.
      rewrite !at_offset_eq.
      rewrite (nested_field_offset_ind t (ArraySubsc i :: gfs))
        by (apply legal_nested_field0_field; simpl; unfold legal_field; rewrite H0; auto).
      rewrite H0.
      subst; auto.
Qed.

Lemma not_ptr_False {prop:bi}: forall  (A : prop) p, (A ⊢ ⌜isptr p⌝) <-> (~ isptr p -> A ⊣⊢ False).
Proof.
  intros.
  split; intros.
  + iSplit; last by iIntros "[]".
    rewrite H; iIntros (?); done.
  + destruct (isptr_dec p); first by iIntros "_".
    rewrite H; last done.
    iIntros "[]".
Qed.

Ltac solve_ptr_derives :=
  repeat rewrite isptr_offset_val;
  apply derives_refl.

Lemma field_at_isptr':
  forall sh t path v c, field_at sh t path v c ⊢ ⌜isptr c⌝.
Proof.
intros.
rewrite field_at_local_facts.
iIntros "(($ & _) & _)".
Qed.

Ltac solve_nptr p A :=
  let H := fresh "H" in
  match A with
  | (?B ∗ ?C) =>
     try solve [assert (~ isptr p -> B ⊣⊢ False) as H by solve_nptr p B;
                intro; rewrite H by auto; apply bi.False_sep];
     try solve [assert (~ isptr p -> C ⊣⊢ False) as H by solve_nptr p C;
                intro; rewrite H by auto; apply bi.sep_False]
  | (?B ∧ ?C) =>
     try solve [assert (~ isptr p -> B ⊣⊢ False) as H by solve_nptr p B;
                intro; rewrite H by auto; apply bi.False_and];
     try solve [assert (~ isptr p -> C ⊣⊢ False) as H by solve_nptr p C;
                intro; rewrite H by auto; apply bi.and_False]
  | _ => apply (proj1 (not_ptr_False A p)); solve_ptr p A
  end
with solve_ptr p A :=
  let p0 := fresh "p" in
  match A with
  | (_ ∗ _) => apply (proj2 (not_ptr_False A p)); solve_nptr p A
  | (_ ∧ _) => apply (proj2 (not_ptr_False A p)); solve_nptr p A
  | ⌜_ /\ _⌝ => destruct A as [_ A]; solve_ptr p A
  | ⌜field_compatible _ _ ?q⌝ => etrans; first apply (bi.pure_mono _ _ (field_compatible_isptr _ _ _)); solve_ptr_derives
  | ⌜field_compatible0 _ _ ?q⌝ => etrans; first apply (bi.pure_mono _ _ (field_compatible0_isptr _ _ _)); solve_ptr_derives
  | (memory_block _ _ ?q) => etrans; first apply (memory_block_local_facts _ _ _); solve_ptr_derives
  | (withspacer _ _ _ ?P p) => apply withspacer_preserve_local_facts;
                                     intro p0; solve_ptr p0 (P p0)
  | (at_offset ?P _ ?q) => trans ⌜isptr q⌝;
                           [apply at_offset_preserve_local_facts; intro p0; solve_ptr p0 (P p0) |
                            solve_ptr_derives]
  | (field_at _ _ _ _ p) => apply field_at_isptr'
  end.

Ltac destruct_ptr p :=
  let b := fresh "b" in
  let ofs := fresh "OFS" in
  match goal with
  | |- ?A ⊣⊢ ?B =>
       let H := fresh "H" in
       let H0 := fresh "H" in
       assert (~ isptr p -> A ⊣⊢ False) as H by solve_nptr p A;
       assert (~ isptr p -> B ⊣⊢ False) as H0 by solve_nptr p B;
       destruct p as [| | | | | b ofs]; try (rewrite H, H0 by (simpl; congruence); reflexivity);
       clear H H0;
       inv_int ofs
  | |- (?A ⊢ _) =>
       let H := fresh "H" in
       assert (~ isptr p -> A ⊣⊢ False) as H by solve_nptr p A;
       destruct p as [| | | | | b ofs]; try (rewrite H by (simpl; congruence); apply bi.False_elim);
       clear H;
       inv_int ofs
  end.

Lemma field_at_Tstruct: forall sh t gfs id a v1 v2 p,
  nested_field_type t gfs = Tstruct id a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p ⊣⊢ nested_sfieldlist_at sh t gfs (co_members (get_co id)) v2 p.
Proof.
  intros.
  unfold field_at, nested_sfieldlist_at.
  revert v1 H0; rewrite H; intros.
  rewrite data_at_rec_eq.
  rewrite at_offset_struct_pred.
  rewrite andp_struct_pred; [| apply _..].
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
    assert (~field_compatible t gfs (Vptr b (Ptrofs.repr ofs)))
     by (clear - n H H1; unfold field_compatible; contradict n; simpl; rewrite H; simpl; tauto).
    assert (~field_compatible t
     (gfs DOT name_member (get_member i (co_members (get_co id))))
     (Vptr b (Ptrofs.repr ofs)))
    by (clear - n H H1; unfold field_compatible; simpl in *; rewrite H in *; simpl in *; tauto).
    rewrite !prop_false_andp by auto; auto.
  }
  f_equiv.
  {
   f_equiv.
   unfold field_compatible.
   do 4 f_equiv.
   simpl.
   split; intro; try tauto. split; auto.
   rewrite H. simpl. rewrite name_member_get. auto.
  }
  replace  (field_offset cenv_cs (name_member (get_member i (co_members (get_co id)))))
   with  (field_offset cenv_cs i)
    by (rewrite name_member_get; auto).
  replace  (field_offset_next cenv_cs (name_member (get_member i (co_members (get_co id)))))
   with  (field_offset_next cenv_cs i)
    by (rewrite name_member_get; auto).
  apply bi.sep_proper.
  f_equiv.
  rewrite name_member_get.
  change (sizeof ?A) with (expr.sizeof A) in *.
  rewrite sizeof_Tstruct. hnf; lia.
  hnf; f_equal. f_equal.
  rewrite name_member_get.  lia.
  match goal with |- data_at_rec _ _ _ ?A ⊣⊢ data_at_rec _ _ _ ?B => replace B with A end.
  2:{ f_equal. f_equal.
  rewrite name_member_get.
  rewrite @nested_field_offset_ind with (gfs := StructField i :: gfs) by auto.
  unfold gfield_offset; rewrite H. lia.
  }
  erewrite data_at_rec_type_changable; first done.
  { rewrite nested_field_type_ind.
    simpl; rewrite H.
    auto. }
  apply (proj_compact_prod_JMeq _ (get_member i _) (co_members (get_co id)) _ _ (unfold_reptype v1) v2); auto.
      * intros.
        rewrite nested_field_type_ind, H.
        unfold gfield_type.
        rewrite In_field_type; auto.
        apply get_co_members_no_replicate.
      * apply in_get_member; auto.
      * clear - H0.
        eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
Qed.

Lemma field_at_Tunion: forall sh t gfs id a v1 v2 p,
  nested_field_type t gfs = Tunion id a ->
  JMeq v1 v2 ->
  field_at sh t gfs v1 p ⊣⊢ nested_ufieldlist_at sh t gfs (co_members (get_co id)) v2 p.
Proof.
  intros.
  unfold field_at, nested_ufieldlist_at.
  revert v1 H0; rewrite H; intros.
  rewrite data_at_rec_eq.
  rewrite at_offset_union_pred.
  rewrite andp_union_pred; [| apply _..].
  generalize (eq_refl (co_members (get_co id))).
  generalize (co_members (get_co id)) at 2 3 9; intro m; destruct m; [auto |].
  intro HH; assert (co_members (get_co id) <> nil) by congruence; clear HH.
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
  unfold field_at, fst, snd.
  autorewrite with at_offset_db.
  unfold offset_val.
  solve_mod_modulus.
  normalize.
  destruct (legal_nested_field_dec t (UnionField i :: gfs)).
  2:{
    rewrite (bi.pure_False (field_compatible t (UnionField _ :: _) _))
      by (rewrite name_member_get; unfold field_compatible; tauto).
    simpl in n.
    rewrite H in n.
    simpl in n.
    rewrite bi.pure_False by (unfold field_compatible; tauto).
    iSplit; iIntros "([] & ?)".
  }
  f_equiv.
  apply bi.pure_iff.
  rewrite name_member_get, field_compatible_cons, H; tauto.
  apply bi.sep_proper.
  rewrite name_member_get.
  f_equiv. rewrite sizeof_Tunion. hnf; lia.
  hnf; f_equal. f_equal. lia.
  match goal with |- data_at_rec _ _ _ ?A ⊣⊢ data_at_rec _ _ _ ?B => replace B with A end.
  2:{ f_equal. f_equal.
  rewrite name_member_get.
  rewrite @nested_field_offset_ind with (gfs := UnionField i :: gfs) by auto.
  unfold gfield_offset; rewrite H. lia.
  }
  erewrite data_at_rec_type_changable; first done.
  rewrite name_member_get.
  rewrite nested_field_type_ind.
  rewrite H; reflexivity.
  unfold proj_union.
      apply (proj_compact_sum_JMeq _ (get_member i _) (co_members (get_co id)) d0 d1 (unfold_reptype v1) v2); auto.
      * intros a0 ?.
        rewrite nested_field_type_ind, H.
        simpl.
        auto.
      * eapply JMeq_trans; [apply (unfold_reptype_JMeq _ v1) | auto].
Qed.

Lemma array_at_len_0: forall sh t gfs i p,
  array_at sh t gfs i i nil p = (⌜field_compatible0 t (ArraySubsc i :: gfs) p⌝ ∧ emp).
Proof.
  intros.
  unfold array_at.
  rewrite array_pred_len_0 by lia.
  f_equal; f_equal; apply prop_ext; tauto.
Qed.

Lemma array_at_len_1: forall sh t gfs i v v' p,
  JMeq v v' ->
  array_at sh t gfs i (i + 1) (v :: nil) p = field_at sh t (ArraySubsc i :: gfs) v' p.
Proof.
  intros.
  unfold array_at, field_at.
  rewrite array_pred_len_1 by lia.
  revert v' H.
  rewrite @nested_field_type_ArraySubsc with (i := i).
  intros.
  apply JMeq_eq in H; rewrite H.
  f_equal; f_equal; apply prop_ext.
  rewrite field_compatible_field_compatible0'.
  reflexivity.
Qed.

Lemma split2_array_at: forall sh t gfs lo mid hi v p,
  lo <= mid <= hi ->
  Zlength v = hi - lo ->
  array_at sh t gfs lo hi v p =
  (array_at sh t gfs lo mid (sublist 0 (mid-lo) v) p ∗
   array_at sh t gfs mid hi (sublist (mid-lo) (Zlength v) v) p).
Proof.
  intros.
  unfold array_at.
  normalize.
  apply andp_prop_eq.
  { destruct (field_compatible0_dec t (gfs SUB lo) p); [|right; tauto].
    destruct (field_compatible0_dec t (gfs SUB hi) p); [left | right]; tauto. }
  + split; [| tauto].
    intros [? ?].
    assert (field_compatible0 t (gfs SUB mid) p) by (apply (field_compatible0_range _ lo hi); auto).
    tauto.
  + intros [? ?].
    rewrite @split_array_pred with (mid := mid) by auto.
    rewrite H0; auto.
Qed.

Lemma split3seg_array_at: forall sh t gfs lo ml mr hi v p,
  lo <= ml ->
  ml <= mr ->
  mr <= hi ->
  Zlength v = hi-lo ->
  array_at sh t gfs lo hi v p =
    (array_at sh t gfs lo ml (sublist 0 (ml-lo) v) p ∗
     array_at sh t gfs ml mr (sublist (ml-lo) (mr-lo) v) p ∗
     array_at sh t gfs mr hi (sublist (mr-lo) (hi-lo) v) p).
Proof.
  intros.
  rewrite split2_array_at with (lo := lo) (mid := ml) (hi := hi) by lia.
  f_equal.
  assert (Zlength (sublist (ml - lo) (hi - lo) v) = hi - ml).
  {
    replace (hi - ml) with (hi - lo - (ml - lo)) by lia.
    apply Zlength_sublist; lia.
  }
  rewrite H2.
  rewrite split2_array_at with (lo := ml) (mid := mr) (hi := hi) by lia.
  f_equal.
  rewrite sublist_sublist; try lia. f_equiv. f_equal; lia.
  rewrite Zlength_sublist by lia.
  rewrite sublist_sublist; try lia. f_equiv. f_equal; lia.
Qed.

Lemma split3_array_at: forall sh t gfs lo mid hi v v0 p,
  lo <= mid < hi ->
  Zlength v = hi-lo ->
  JMeq v0 (Znth (mid-lo) v) ->
  array_at sh t gfs lo hi v p =
    (array_at sh t gfs lo mid (sublist 0 (mid-lo) v) p ∗
     field_at sh t (ArraySubsc mid :: gfs) v0 p ∗
     array_at sh t gfs (mid + 1) hi (sublist (mid+1-lo) (hi-lo) v) p).
Proof.
  intros.
  rename H0 into e; rename H1 into H0.
  rewrite split3seg_array_at with (ml := mid) (mr := mid + 1) by lia.
  f_equal. f_equal.
  replace (mid + 1 - lo) with (mid - lo + 1) by lia.
  rewrite sublist_len_1 by lia.
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
  + f_equal.
    * f_equal.
      apply prop_ext; split; auto.
      apply field_compatible_nested_field.
    * unfold at_offset.
      rewrite isptr_offset_val_zero by (destruct H; auto).
      done.
  + rewrite !prop_false_andp; auto.
    intros (? & ?); contradiction.
Qed.

Lemma field_at_data_at' : forall sh t gfs v p, field_at sh t gfs v p =
  (⌜field_compatible t gfs p⌝ ∧
   data_at sh (nested_field_type t gfs) v (offset_val (nested_field_offset t gfs) p)).
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
  intros. apply field_at_data_at.
Qed.

Lemma lifted_field_at_data_at: forall sh t gfs v p,
  assert_of (`(field_at sh t gfs) v p) =
  assert_of (`(data_at sh (nested_field_type t gfs)) v (`(field_address t gfs) p)).
Proof.
  intros.
  apply assert_ext; intros; unfold_lift.
  apply field_at_data_at.
Qed.

Lemma lifted_field_at__data_at_: forall sh t gfs p,
  assert_of (`(field_at_ sh t gfs) p) =
  assert_of (`(data_at_ sh (nested_field_type t gfs)) (`(field_address t gfs) p)).
Proof.
  intros.
  apply assert_ext; intros; unfold_lift.
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
  (⌜field_compatible0 t (ArraySubsc lo :: gfs) p⌝ ∧
  ⌜field_compatible0 t (ArraySubsc hi :: gfs) p⌝ ∧
  at_offset (data_at sh (nested_field_array_type t gfs lo hi) v)
               (nested_field_offset t (ArraySubsc lo :: gfs)) p).
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
  apply andp_prop_eq.
  { destruct (field_compatible0_dec t (gfs SUB lo) p); [|right; tauto].
    destruct (field_compatible0_dec t (gfs SUB hi) p); [left | right]; tauto. }
  + pose proof field_compatible0_nested_field_array t gfs lo hi p.
    tauto.
  + intros (? & ?).
    rewrite at_offset_eq, <- at_offset_eq2.
    rewrite at_offset_array_pred.
    rewrite Z.max_r by lia.
    eapply array_pred_shift; [reflexivity | lia |].
    intros.
    rewrite at_offset_eq at 1.
    rewrite at_offset_eq, <- at_offset_eq2, at_offset_eq.
    f_equiv.
    f_equiv.
    rewrite @nested_field_offset_ind with (gfs := nil) by (apply (field_compatible0_nested_field_array t gfs lo hi p); auto).
    assert (field_compatible0 t (gfs SUB i') p) as Hcompat
      by (apply (field_compatible0_range _ lo hi); auto; lia).
    rewrite @nested_field_offset_ind with (gfs := ArraySubsc i' :: _) by auto.
    rewrite @nested_field_offset_ind with (gfs := ArraySubsc lo :: _) by auto.
    rewrite @nested_field_type_ind with (gfs := ArraySubsc 0 :: _).
    rewrite field_compatible0_cons in Hcompat.
    destruct (nested_field_type t gfs); try tauto.
    unfold gfield_offset, gfield_type.
    assert (sizeof t0 * i' = sizeof t0 * lo + sizeof t0 * i)%Z by (rewrite Zred_factor4; f_equal; lia).
    hnf; lia.
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
  f_equiv.
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
  + rewrite (data_at_isptr _ _ _ Vundef).
    rewrite !prop_false_andp by auto; done.
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
      lia.
    - rewrite !prop_true_andp by auto.
      auto.
  + rewrite (data_at_isptr _ _ _ Vundef).
    rewrite !prop_false_andp by auto; done.
Qed.

Lemma split3seg_array_at': forall sh t gfs lo ml mr hi v p,
  lo <= ml ->
  ml <= mr ->
  mr <= hi ->
  Zlength v = hi-lo ->
  array_at sh t gfs lo hi v p =
    (array_at sh t gfs lo ml (sublist 0 (ml-lo) v) p ∗
     data_at sh (nested_field_array_type t gfs ml mr)
        (sublist (ml-lo) (mr-lo) v)
               (field_address0 t (ArraySubsc ml::gfs) p) ∗
     array_at sh t gfs mr hi (sublist (mr-lo) (hi-lo) v) p).
Proof.
  intros.
  rewrite (split3seg_array_at sh t gfs lo ml mr hi); auto.
  unfold array_at at 3 5; normalize.
  apply andp_prop_eq1.
  { destruct (field_compatible0_dec t (gfs SUB mr) p); [|right; tauto].
    destruct (field_compatible0_dec t (gfs SUB hi) p); [left | right]; tauto. }
  intros (? & ?).
  rewrite (array_at_data_at'' sh t gfs ml mr); auto.
Qed.

(************************************************

Lemmas about underscore and memory_block

************************************************)

Lemma field_at_field_at_: forall sh t gfs v p,
  field_at sh t gfs v p ⊢ field_at_ sh t gfs p.
Proof.
  intros.
  destruct (field_compatible_dec t gfs p).
  + destruct_ptr p.
    unfold field_at_, field_at.
    apply bi.and_mono; first done.
    pose proof field_compatible_nested_field _ _ _ f.
    unfold field_compatible in H, f.
    unfold offset_val in H.
    autorewrite with at_offset_db in *.
    unfold align_compatible, size_compatible in *.
    revert H f; solve_mod_modulus; intros.
    pose proof nested_field_offset_in_range t gfs.
    spec H1; [tauto |].
    spec H1; [tauto |].
    change (sizeof ?A) with (expr.sizeof A) in *.
    rewrite (Z.mod_small ofs) in * by lia.
    rewrite (Z.mod_small (ofs + nested_field_offset t gfs)) in H
        by (pose proof base.sizeof_pos (nested_field_type t gfs); lia).
    apply data_at_rec_data_at_rec_; try tauto.
    unfold expr.sizeof in *.
    lia.
  + unfold field_at_, field_at.
    normalize.
Qed.

Lemma field_at_field_at_default : forall sh t gfs v v' p,
  v' = default_val (nested_field_type t gfs) ->
  field_at sh t gfs v p ⊢ field_at sh t gfs v' p.
Proof.
  intros; subst.
  apply field_at_field_at_.
Qed.

Lemma field_at__memory_block: forall sh t gfs p,
  field_at_ sh t gfs p ⊣⊢
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
    change (sizeof ?A) with (expr.sizeof A) in *.
    rewrite (Z.mod_small ofs) in * by lia.
    rewrite (Z.mod_small (ofs + nested_field_offset t gfs)) in H by (pose proof base.sizeof_pos (nested_field_type t gfs); lia).
    rewrite memory_block_data_at_rec_default_val; first done; try tauto; unfold expr.sizeof in *; try lia.
  + unfold field_at_, field_at.
    rewrite memory_block_isptr.
    apply bi.equiv_entails_2; normalize.
Qed.

Lemma mapsto_zero_data_at_zero:
  forall t sh p,
    readable_share sh ->
    complete_legal_cosu_type t = true ->
    fully_nonvolatile (rank_type cenv_cs t) t = true ->
    field_compatible t nil p ->
    mapsto_zeros (sizeof t) sh p ⊢ data_at sh t (zero_val t) p.
Proof.
intros.
unfold data_at, field_at.
rewrite prop_true_andp by auto.
destruct H2 as [? [? [? [? ?]]]].
unfold nested_field_offset, nested_field_rec.
unfold at_offset.
normalize.
destruct p; try contradiction.
rewrite <- (Ptrofs.repr_unsigned i).
apply mapsto_zeros_data_at_rec_zero_val; auto.
red in H4.
rep_lia.
Qed.

Lemma data_at_data_at_ : forall sh t v p,
  data_at sh t v p ⊢ data_at_ sh t p.
Proof.
  intros.
  apply field_at_field_at_.
Qed.

Lemma data_at_data_at_default : forall sh t v v' p,
  v' = default_val (nested_field_type t nil) ->
  data_at sh t v p ⊢ data_at sh t v' p.
Proof.
  intros; subst.
  apply data_at_data_at_.
Qed.

Lemma data_at__memory_block: forall sh t p,
  data_at_ sh t p ⊣⊢
  (⌜field_compatible t nil p⌝ ∧ memory_block sh (sizeof t) p).
Proof.
  intros.
  unfold data_at_, data_at.
  rewrite field_at__memory_block.
  unfold field_address.
  if_tac.
  + normalize.
  + unfold field_at_, field_at.
    rewrite memory_block_isptr.
    rewrite bi.pure_False by auto.
    rewrite (bi.pure_False _ H).
    iSplit; iIntros "([] & _)".
Qed.

Lemma memory_block_data_at_: forall sh t p,
  field_compatible t nil p ->
  memory_block sh (sizeof t) p ⊣⊢ data_at_ sh t p.
Proof.
  intros.
  rewrite data_at__memory_block.
  normalize.
Qed.

Lemma data_at__memory_block_cancel:
   forall sh t p,
       data_at_ sh t p ⊢ memory_block sh (sizeof t) p.
Proof.
  intros.
  rewrite data_at__memory_block.
  normalize.
Qed.

Lemma data_at_memory_block:
  forall sh t v p,
     data_at sh t v p ⊢ memory_block sh (sizeof t) p.
Proof.
  intros.
  rewrite data_at_data_at_.
  rewrite data_at__memory_block by auto.
  iIntros "(_ & $)".
Qed.

Lemma array_at_array_at_: forall sh t gfs lo hi v p,
  array_at sh t gfs lo hi v p ⊢ array_at_ sh t gfs lo hi p.
Proof.
  intros.
  iIntros "H".
  iDestruct (array_at_local_facts with "H") as %H.
  iApply (array_at_ext_derives with "H").
  { rewrite Zlength_Zrepeat by (rewrite Zlength_correct in H; lia); lia. }
  intros.
  destruct (field_compatible0_dec t (ArraySubsc i :: gfs) p).
  + generalize dependent u1; erewrite <- @nested_field_type_ArraySubsc with (i := i).
    intros ? ->%JMeq_eq. unfold Znth. rewrite if_false by lia.
    unfold Zrepeat; rewrite nth_repeat.
    apply field_at_field_at_; auto.
  + unfold field_at.
    normalize.
    contradiction n; apply field_compatible_field_compatible0; done.
Qed.

Lemma withspacer_field_at__Tunion: forall sh t gfs i id a p,
  nested_field_type t gfs = Tunion id a ->
  in_members i (co_members (get_co id)) ->
  withspacer sh
   (nested_field_offset t gfs +
    sizeof (field_type i (co_members (get_co id))))
   (nested_field_offset t gfs + sizeof (nested_field_type t gfs))
   (field_at_ sh t (gfs UDOT i)) p ⊣⊢
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
    apply bi.equiv_entails_2; normalize.
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
  + pose proof sizeof_pos (field_type i (co_members (get_co id))); lia.
  + lia.
  + change (sizeof ?A) with (expr.sizeof A) in *.
    split.
    - rewrite sizeof_Tunion.
      erewrite co_consistent_sizeof by apply get_co_consistent.
      rewrite @complete_legal_cosu_type_Tunion with (a := a)
        by (rewrite <- H; apply nested_field_type_complete_legal_cosu_type;
            unfold field_compatible in *; tauto).
      pose proof align_le (sizeof_composite cenv_cs Union (co_members (get_co id)))
           (co_alignof (get_co id)) (co_alignof_pos _).
      unfold sizeof_composite in *.
      pose proof sizeof_union_in_members _ _ H0.
      unfold expr.sizeof in *.
      lia.
    - rewrite <- H.
      unfold field_compatible in *.
      unfold size_compatible in *.
      revert H1; solve_mod_modulus; intros.
      rewrite Zmod_small in H1 by lia.
      lia.
  + rewrite <- H.
    unfold field_compatible, size_compatible in *.
    rewrite Ptrofs.unsigned_repr in * by (unfold Ptrofs.max_unsigned; lia).
    unfold expr.sizeof in *.
    lia.
Qed.

Lemma array_at_ramif: forall sh t gfs t0 n a lo hi i v v0 p,
  nested_field_type t gfs = Tarray t0 n a ->
  lo <= i < hi ->
  JMeq v0 (Znth (i - lo) v) ->
  array_at sh t gfs lo hi v p ⊢ field_at sh t (ArraySubsc i :: gfs) v0 p ∗
   ∀ v0 v0', ⌜JMeq v0 v0'⌝ →
      (field_at sh t (ArraySubsc i :: gfs) v0 p -∗
        array_at sh t gfs lo hi (upd_Znth (i - lo) v v0') p).
Proof.
  intros.
  iIntros "H".
  iDestruct (array_at_local_facts with "H") as %(? & ? & ? & ?).
  erewrite (split3_array_at sh t gfs lo i hi) by (eauto; lia).
  iDestruct "H" as "(? & $ & ?)".
  clear dependent v0.
  iIntros (v0 v0' ?) "?".
  erewrite (split3_array_at sh t gfs lo i hi).
  2: auto.
  2:{ rewrite upd_Znth_Zlength by lia.
      auto. }
  2:{ rewrite upd_Znth_same by lia.
      done. }
  rewrite @sublist_upd_Znth_l with (lo := 0) by lia.
  rewrite @sublist_upd_Znth_r with (lo := (i + 1 - lo)) by lia.
  iFrame.
Qed.

Lemma nested_sfieldlist_at_ramif: forall sh t gfs id a i v p,
  let d := default_val _ in
  nested_field_type t gfs = Tstruct id a ->
  in_members i (co_members (get_co id)) ->
  nested_sfieldlist_at sh t gfs (co_members (get_co id)) v p ⊢
  field_at sh t (StructField (name_member (get_member i (co_members (get_co id)))) :: gfs)
    (proj_struct i (co_members (get_co id)) v d) p ∗
      (∀ v0,
         field_at sh t (StructField (name_member (get_member i (co_members (get_co id)))) :: gfs) v0 p -∗
           nested_sfieldlist_at sh t gfs (co_members (get_co id))
            (upd_struct i (co_members (get_co id)) v v0) p).
Proof.
  intros.
  pose proof (get_co_members_no_replicate id).
  forget (co_members (get_co id)) as m.
  destruct m; [inv H0|].
  revert v d H0; intros.
  unfold nested_sfieldlist_at.
  etrans.
  { apply (struct_pred_ramif (m::m0)
            (fun it v p =>
              withspacer sh
                (nested_field_offset t gfs +
                (field_offset cenv_cs (name_member it) (m::m0) +
                 sizeof (field_type (name_member it) (m::m0))))
                (nested_field_offset t gfs +
                 field_offset_next cenv_cs (name_member it) (m::m0)
                   (sizeof (nested_field_type t gfs)))
                (field_at sh t (gfs DOT name_member it) v) p)); eauto. }
  iIntros "(H & H1)".
  iDestruct (withspacer_ramif_Q with "H") as "($ & H2)".
  iIntros (?) "?"; iApply "H1"; iApply "H2"; done.
Qed.

Lemma nested_ufieldlist_at_ramif: forall sh t gfs id a i v p,
  let d := default_val _ in
  nested_field_type t gfs = Tunion id a ->
  in_members i (co_members (get_co id)) ->
  nested_ufieldlist_at sh t gfs (co_members (get_co id)) v p ⊢
  field_at sh t (UnionField (name_member (get_member i (co_members (get_co id)))) :: gfs)
    (proj_union i (co_members (get_co id)) v d) p ∗
      (∀ v0,
         field_at sh t (UnionField (name_member (get_member i (co_members (get_co id)))) :: gfs) v0 p -∗
           nested_ufieldlist_at sh t gfs (co_members (get_co id))
            (upd_union i (co_members (get_co id)) v v0) p).
Proof.
  intros.
  pose proof (get_co_members_no_replicate id).
  destruct (co_members (get_co id)) eqn:?; [inv H0|].
  revert v d H0; intros.
  unfold nested_ufieldlist_at.
  etrans.
  { apply (union_pred_ramif (m::m0)
            (fun it v p =>
              withspacer sh
                (nested_field_offset t gfs +
                 sizeof
                   (field_type (name_member it) (m::m0)))
                (nested_field_offset t gfs +
                 sizeof (nested_field_type t gfs))
                (field_at sh t (gfs UDOT name_member it) v) p)); try done.
    instantiate (1 := default_val _).
    intros.
    rewrite !withspacer_spacer.
    unfold fst.
    fold (field_at_ sh t (gfs UDOT i) p).
    rewrite field_at_field_at_.
    rewrite <- !withspacer_spacer.
    rewrite name_member_get.
    rewrite <- Heqm.
    erewrite !withspacer_field_at__Tunion; try eassumption; auto.
    rewrite name_member_get. rewrite Heqm. auto.
    rewrite Heqm; auto.
  }
  iIntros "(H & H1)".
  iDestruct (withspacer_ramif_Q with "H") as "($ & H2)".
  iIntros (?) "?"; iApply "H1"; iApply "H2"; done.
Qed.

Lemma memory_block_valid_ptr:
  forall sh n p,
     sh ≠ Share.bot ->
     n > 0 ->
     memory_block sh n p ⊢ valid_pointer p.
Proof.
  intros.
  rewrite memory_block_isptr.
  normalize.
  destruct p; try tauto.
  inv_int i.
  replace (Vptr b (Ptrofs.repr ofs)) with (offset_val 0 (Vptr b (Ptrofs.repr ofs))) at 2.
  + apply memory_block_valid_pointer with (i := 0); auto; lia.
  + simpl.
    rewrite ptrofs_add_repr, Z.add_0_r.
    auto.
Qed.

Lemma data_at__valid_ptr:
  forall sh t p,
     sh ≠ Share.bot ->
     sizeof t > 0 ->
     data_at_ sh t p ⊢ valid_pointer p.
Proof.
  intros.
  rewrite data_at__memory_block.
  normalize.
  apply memory_block_valid_ptr; auto.
Qed.

Lemma data_at_valid_ptr:
  forall sh t v p,
     sh ≠ Share.bot ->
     sizeof t > 0 ->
     data_at sh t v p ⊢ valid_pointer p.
Proof.
  intros.
  rewrite data_at_data_at_.
  apply data_at__valid_ptr; auto.
Qed.

Lemma field_at_valid_ptr:
  forall sh t path v p,
     sh ≠ Share.bot ->
     sizeof (nested_field_type t path) > 0 ->
     field_at sh t path v p ⊢ valid_pointer (field_address t path p).
Proof.
intros.
rewrite field_at_data_at.
apply data_at_valid_ptr; auto.
Qed.

Lemma field_at_valid_ptr0:
  forall sh t path v p,
     sh ≠ Share.bot ->
     sizeof (nested_field_type t path) > 0 ->
     nested_field_offset t path = 0 ->
     field_at sh t path v p ⊢ valid_pointer p.
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

Lemma compute_legal_nested_field_spec {prop:bi}: forall (P: prop) t gfs,
  Forall (fun Q => P ⊢ ⌜Q⌝) (compute_legal_nested_field t gfs) ->
  P ⊢ ⌜legal_nested_field t gfs⌝.
Proof.
  intros.
  induction gfs as [| gf gfs].
  + simpl.
    by iIntros "?".
  + simpl in H |- *.
    unfold legal_field.
    destruct (nested_field_type t gfs), gf; inversion H; subst;
    try
    match goal with
    | HH : P ⊢ ⌜False⌝ |-
           P ⊢ ⌜_⌝ => rewrite HH; apply bi.pure_mono; tauto
    end.
    - apply IHgfs in H3.
      rewrite (add_andp _ _ H2).
      rewrite (add_andp _ _ H3).
      normalize.
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H as ->.
        apply bi.pure_mono; tauto.
      * inversion H1.
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H as ->.
        apply bi.pure_mono; tauto.
      * inv H.
        rewrite H6; iIntros "[]".
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H as ->.
        apply bi.pure_mono; tauto.
      * inversion H1.
    - destruct_in_members i0 (co_members (get_co i)).
      * apply IHgfs in H as ->.
        apply bi.pure_mono; tauto.
      * inv H.
        rewrite H6; iIntros "[]".
Qed.


Lemma compute_legal_nested_field_spec':
  forall t gfs,
  Forall Datatypes.id (compute_legal_nested_field t gfs) ->
  legal_nested_field t gfs.
Proof.
  intros.
  induction gfs as [| gf gfs].
  + simpl; auto.
  + simpl in H|-*.
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
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs else False%type :: nil
    | Tunion id _, UnionField i =>
       if compute_in_members i (co_members (get_co id)) then compute_legal_nested_field t gfs else False%type :: nil
    | _, _ => False%type :: nil
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

Lemma field_at_share_joins: forall sh1 sh2 t fld p v,
  0 < sizeof (nested_field_type t fld) ->
  field_at sh1 t fld v p ∗ field_at sh2 t fld v p ⊢ ⌜sepalg.joins sh1 sh2⌝.
Proof.
  intros.
  rewrite field_at_compatible'.
  iIntros "(((% & % & % & % & %) & H1) & H2)".
  destruct (nested_field_offset_in_range t fld); [done..|].
  assert (0 < sizeof (nested_field_type t fld) < Ptrofs.modulus).
  {
    destruct p; try done.
    simpl in *.
    inv_int i.
    unfold expr.sizeof in *.
    lia.
  }
  rewrite !field_at_field_at_.
  rewrite !field_at__memory_block by auto.
  iApply (memory_block_share_joins with "[$H1 $H2]"); lia.
Qed.

Lemma field_at_conflict: forall sh t fld p v v',
  sh ≠ Share.bot ->
  0 < sizeof (nested_field_type t fld) ->
  field_at sh t fld v p ∗ field_at sh t fld v' p ⊢ False.
Proof.
  intros.
  rewrite field_at_compatible'.
  iIntros "(((% & % & % & % & %) & ?) & ?)".
  destruct (nested_field_offset_in_range t fld); [done..|].
  assert (0 < sizeof (nested_field_type t fld) < Ptrofs.modulus).
  {
    destruct p; try done.
    simpl in *.
    inv_int i.
    unfold expr.sizeof in *.
    lia.
  }
  rewrite !field_at_field_at_.
  rewrite field_at__memory_block by auto.
  iApply (memory_block_conflict with "[$]"); first done; unfold Ptrofs.max_unsigned; lia.
Qed.

Lemma data_at_share_joins: forall sh1 sh2 t v p,
  0 < sizeof t ->
  data_at sh1 t v p ∗ data_at sh2 t v p ⊢ ⌜sepalg.joins sh1 sh2⌝.
Proof.
  intros. unfold data_at. apply field_at_share_joins; auto.
Qed.

Lemma data_at_conflict: forall sh t v v' p,
  sh ≠ Share.bot ->
  0 < sizeof t ->
  data_at sh t v p ∗ data_at sh t v' p ⊢ False.
Proof.
  intros. unfold data_at. apply field_at_conflict; auto.
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  sh ≠ Share.bot ->
  0 < sizeof (nested_field_type t fld) ->
        field_at_ sh t fld p
        ∗ field_at_ sh t fld p ⊢ False.
Proof.
intros.
apply field_at_conflict; auto.
Qed.

Lemma sepcon_False_derives' {prop:bi}:
  forall (P Q: prop), (Q ⊢ False) -> P ∗ Q ⊢ False.
Proof.
  intros ?? ->.
  iIntros "(_ & [])".
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
if_tac; intuition (auto; try solve [contradiction]).
Qed.

Lemma isptr_field_address_lemma:
 forall t path p,
   isptr (field_address t path p) <->
   field_compatible t path p.
Proof.
intros.
unfold field_address.
if_tac; intuition (auto; try solve [contradiction]).
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
  var_block sh (id, t) ⊣⊢ assert_of (`(data_at_ sh t) (eval_lvar id t)).
Proof.
  intros; split => rho.
  unfold var_block; monPred.unseal.
  unfold_lift; simpl.
  apply Zlt_is_lt_bool in H0.
  rewrite data_at__memory_block; try auto.
  rewrite memory_block_isptr.
  unfold local, lift1; unfold_lift.
  pose proof eval_lvar_spec id t rho.
  destruct (eval_lvar id t rho); simpl in *; normalize.
  { iSplit; iIntros "((_ & []) & _)". }
  subst.
  apply bi.and_proper; last done.
  apply bi.pure_iff.
  unfold field_compatible.
  unfold isptr, legal_nested_field, size_compatible, align_compatible.
  change (Ptrofs.unsigned Ptrofs.zero) with 0.
  rewrite Z.add_0_l.
  assert (sizeof t <= Ptrofs.modulus) by lia.
  assert (sizeof t <= Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
  apply la_env_cs_sound in H1; tauto.
Qed.

Lemma valid_pointer_weak:
 forall a, valid_pointer a ⊢ weak_valid_pointer a.
Proof.
intros.
unfold valid_pointer, weak_valid_pointer; auto.
Qed.

Lemma valid_pointer_weak':
  forall P q, (P ⊢ valid_pointer q) ->
                 P ⊢ weak_valid_pointer q.
Proof.
intros.
rewrite <- valid_pointer_weak; done.
Qed.

Lemma valid_pointer_offset_zero: forall P q,
   (P ⊢ valid_pointer (offset_val 0 q)) ->
   P ⊢ valid_pointer q.
Proof.
intros.
destruct q; auto.
- rewrite H.
  simpl valid_pointer.
  iIntros "[]".
- rewrite offset_val_zero_Vptr in H.
  auto.
Qed.

End CENV.

#[export] Hint Extern 2 (memory_block _ _ _ ⊢ valid_pointer _) =>
  (apply memory_block_valid_ptr; [auto with valid_pointer | rep_lia]) : valid_pointer.

#[export] Hint Resolve valid_pointer_weak' : valid_pointer.

#[export] Hint Extern 1 (_ ⊢ valid_pointer ?Q) =>
  lazymatch Q with
  | offset_val _ _ => fail
  | _ => apply valid_pointer_offset_zero
  end : core.

#[export] Hint Extern 2 (memory_block _ _ _ ⊢ weak_valid_pointer _) =>
  (apply memory_block_weak_valid_pointer;
        [rep_lia | rep_lia | auto with valid_pointer]) : valid_pointer.

Local Set SsrRewrite. (* for rewrite bi._ to work *)
Ltac field_at_conflict z fld :=
 apply (derives_trans _ False); [ | apply bi.False_elim];
 repeat rewrite bi.sep_assoc;
 unfold data_at_, data_at, field_at_;
 let x := fresh "x" in set (x := field_at _ _ fld _ z); pull_right x;
 let y := fresh "y" in set (y := field_at _ _ fld _ z); pull_right y;
 try (rewrite <- bi.sep_assoc; eapply sepcon_False_derives');
 subst x y;
 apply field_at_conflict; auto;
 try solve [simpl;  (* This simpl seems safe enough, it's just simplifying (sizeof (nested_field_type _ _))
                                  and in any case it's followed by (computable) *)
                computable].

Ltac data_at_conflict z := field_at_conflict z (@nil gfield).

Ltac data_at_conflict_neq_aux1 A sh fld E x y :=
   match A with
   | context [data_at sh _ _ y] => unify fld (@nil gfield)
   | context [data_at_ sh _ y]  => unify fld (@nil gfield)
   | context [field_at sh _ fld _ y] => idtac
   | context [field_at_ sh _ fld y]  => idtac
   end;
   trans (⌜~ E⌝ ∧ A);
   [apply bi.and_intro; [ | apply derives_refl];
    let H := fresh in
    apply not_prop_right; intro H;
    (rewrite H || rewrite (ptr_eq_e _ _ H));
    field_at_conflict y fld
   | apply bi.pure_elim_l;
     (* for this tactic to succeed, it must introduce a new hyp H1,
        but rewriting H1 can fail, as the goal might be _-∗⌜C[~E]⌝
        for some context C *)
     let H1 := fresh in fancy_intro H1;
     rewrite ->?(bi.pure_True (~E)) by assumption
    ].

Ltac data_at_conflict_neq_aux2 A E x y :=
   match A with
   | context [data_at ?sh _ _ x] => data_at_conflict_neq_aux1 A sh (@nil gfield) E x y
   | context [data_at_ ?sh _ x]  => data_at_conflict_neq_aux1 A sh (@nil gfield) E x y
   | context [field_at ?sh _ ?fld _ x] => data_at_conflict_neq_aux1 A sh fld E x y
   | context [field_at_ ?sh _ ?fld x]  => data_at_conflict_neq_aux1 A sh fld E x y
   end.

Ltac data_at_conflict_neq :=
  match goal with |- ?A ⊢ ?B =>
   match B with
   | context [?x <> ?y] => data_at_conflict_neq_aux2 A (x=y) x y
   | context [~ ptr_eq ?x ?y] => data_at_conflict_neq_aux2 A (ptr_eq x y) x y
   end
  end.
Local Unset SsrRewrite.

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
  replace ofs with (ofs - 0) in H1 by lia.
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
repeat split; simpl; auto; try lia.
Qed.

#[export] Hint Extern 2 (field_compatible _ nil _) =>
 (apply malloc_compatible_field_compatible;
  [assumption | reflexivity | reflexivity]) : core.

Section local_facts.

Context `{!VSTGS OK_ty Σ}.

Lemma data_array_at_local_facts {cs: compspecs}:
 forall t' n a sh (v: list (reptype t')) p,
  data_at sh (Tarray t' n a) v p ⊢
  ⌜field_compatible (Tarray t' n a) nil p
     /\ Zlength v = Z.max 0 n
     /\ Forall (value_fits t') v⌝.
Proof.
intros.
rewrite data_at_local_facts.
apply bi.pure_mono.
intros [? ?]; split; auto.
Qed.

Lemma data_array_at_local_facts' {cs: compspecs}:
 forall t' n a sh (v: list (reptype t')) p,
  n >= 0 ->
  data_at sh (Tarray t' n a) v p ⊢
  ⌜field_compatible (Tarray t' n a) nil p
     /\ Zlength v = n
     /\ Forall (value_fits t') v⌝.
Proof.
intros.
rewrite data_array_at_local_facts.
apply bi.pure_mono.
intros [? [? ?]]; split3; auto.
rewrite Z.max_r in H1 by lia. auto.
Qed.

End local_facts.

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
match goal with |- field_at ?sh ?t ?path ?v ?c ⊢ _ =>
rewrite field_at_local_facts;
  let p := fresh "p" in set (p := nested_field_type t path);
  simpl in p; unfold field_type in p; simpl in p; subst p;  (* these simpls are probably not dangerous *)
  try rewrite value_fits_by_value by reflexivity;
  try match goal with |- context [repinject ?t ?v] =>
    change (repinject t v) with v
  end;
  apply derives_refl
end.

Ltac data_at_valid_aux :=
 first [computable | unfold sizeof; simpl Ctypes.sizeof; rewrite ?Z.max_r by rep_lia; rep_lia | rep_lia].

#[export] Hint Extern 1 (data_at _ _ _ _ ⊢ valid_pointer _) =>
    (simple apply data_at_valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

#[export] Hint Extern 1 (field_at _ _ _ _ _ ⊢ valid_pointer _) =>
    (simple apply field_at_valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

#[export] Hint Extern 1 (data_at_ _ _ _ ⊢ valid_pointer _) =>
    (simple apply data_at__valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

#[export] Hint Extern 1 (field_at_ _ _ _ _ ⊢ valid_pointer _) =>
    (apply field_at_valid_ptr; [now auto | data_at_valid_aux]) : valid_pointer.

#[export] Hint Extern 1 (field_at _ _ _ _ _ ⊢ _) =>
 (field_at_saturate_local) : saturate_local.

#[export] Hint Extern 1 (data_at _ _ _ _ ⊢ _) =>
 (field_at_saturate_local) : saturate_local.

#[export] Hint Resolve array_at_local_facts array_at__local_facts : saturate_local.

#[export] Hint Resolve field_at__local_facts : saturate_local.
#[export] Hint Resolve data_at__local_facts : saturate_local.
#[export] Hint Extern 0 (data_at _ (Tarray _ _ _) _ _ ⊢ _) =>
  (apply data_array_at_local_facts'; lia) : saturate_local.
#[export] Hint Extern 0 (data_at _ (tarray _ _) _ _ ⊢ _) =>
  (apply data_array_at_local_facts'; lia) : saturate_local.
#[export] Hint Extern 1 (data_at _ (Tarray _ _ _) _ _ ⊢ _) =>
  (apply data_array_at_local_facts) : saturate_local.
#[export] Hint Extern 1 (data_at _ (tarray _ _) _ _ ⊢ _) =>
  (apply data_array_at_local_facts) : saturate_local.
#[export] Hint Rewrite <- @field_at_offset_zero: norm1.
#[export] Hint Rewrite <- @field_at__offset_zero: norm1.
#[export] Hint Rewrite <- @field_at_offset_zero: cancel.
#[export] Hint Rewrite <- @field_at__offset_zero: cancel.
#[export] Hint Rewrite <- @data_at__offset_zero: norm1.
#[export] Hint Rewrite <- @data_at_offset_zero: norm1.
#[export] Hint Rewrite <- @data_at__offset_zero: cancel.
#[export] Hint Rewrite <- @data_at_offset_zero: cancel.


(* We do these as specific lemmas, rather than
  as Hint Resolve derives_refl, to limit their application
  and make them fail faster *)

Section cancel.

Context `{!VSTGS OK_ty Σ}.

Lemma data_at_cancel:
  forall {cs: compspecs} sh t v p,
    data_at sh t v p ⊢ data_at sh t v p.
Proof. intros. apply derives_refl. Qed.
Lemma field_at_cancel:
  forall {cs: compspecs} sh t gfs v p,
    field_at sh t gfs v p ⊢ field_at sh t gfs v p.
Proof. intros. apply derives_refl. Qed.

Lemma data_at_field_at_cancel:
  forall {cs: compspecs} sh t v p,
    data_at sh t v p ⊢ field_at sh t nil v p.
Proof. intros. apply derives_refl. Qed.
Lemma field_at_data_at_cancel:
  forall {cs: compspecs} sh t v p,
    field_at sh t nil v p ⊢ data_at sh t v p.
Proof. intros. apply derives_refl. Qed.

Lemma field_at__data_at__cancel:
  forall {cs: compspecs} sh t p,
   field_at_ sh t nil p ⊢ data_at_ sh t p.
Proof. intros. apply derives_refl. Qed.

Lemma data_at__field_at__cancel:
  forall {cs: compspecs} sh t p,
   data_at_ sh t p ⊢ field_at_ sh t nil p.
Proof. intros. apply derives_refl. Qed.

End cancel.

#[export] Hint Resolve data_at_cancel field_at_cancel
   data_at_field_at_cancel field_at_data_at_cancel : cancel.

#[export] Hint Resolve  field_at__data_at__cancel data_at__field_at__cancel : cancel.

(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

#[export] Hint Extern 2 (field_at _ _ _ _ _ ⊢ field_at_ _ _ _ _) =>
   (simple apply field_at_field_at_) : cancel.

#[export] Hint Extern 2 (field_at _ _ _ _ _ ⊢ field_at _ _ _ _ _) =>
  (simple apply field_at_field_at_default;
   match goal with |- _ = default_val _ => reflexivity end) : cancel.

#[export] Hint Extern 1 (data_at _ _ _ _ ⊢ data_at_ _ _ _) =>
    (simple apply data_at_data_at_) : cancel.

#[export] Hint Extern 1 (data_at _ _ _ _ ⊢ memory_block _ _ _) =>
    (simple apply data_at__memory_block_cancel) : cancel.

#[export] Hint Extern 2 (data_at _ _ _ _ ⊢ data_at _ _ _ _) =>
  (simple apply data_at_data_at_default;
   match goal with |- _ = default_val _ => reflexivity end) : cancel.

(* too slow this way.
#[export] Hint Extern 2 (data_at _ _ _ _ ⊢ data_at _ _ _ _) =>
  (apply data_at_data_at_default; reflexivity) : cancel.
*)

#[export] Hint Extern 2 (array_at _ _ _ _ _ _ _ ⊢ array_at_ _ _ _ _ _ _) =>
  (simple apply array_at_array_at_) : cancel.
#[export] Hint Extern 1 (isptr _) => (eapply field_compatible_offset_isptr; eassumption) : core.
#[export] Hint Extern 1 (isptr _) => (eapply field_compatible0_offset_isptr; eassumption) : core.
#[export] Hint Rewrite @is_pointer_or_null_field_address_lemma : entailer_rewrite.
#[export] Hint Rewrite @isptr_field_address_lemma : entailer_rewrite.

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

Definition field_at_mark `{!VSTGS OK_ty Σ} cs := field_at(cs := cs).
Definition field_at_hide `{!VSTGS OK_ty Σ} cs  := field_at(cs := cs).
Definition data_at_hide `{!VSTGS OK_ty Σ} cs  := data_at(cs := cs).

Ltac find_field_at N :=
 match N with
 | S O =>  change (field_at(cs := ?cs)) with (field_at_mark cs) at 1;
              change (field_at_hide ?cs) with (field_at(cs := cs))
 | S ?k => change (field_at(cs := ?cs)) with (field_at_hide cs) at 1;
                find_field_at k
 end.

Ltac find_data_at N :=
 match N with
 | S O =>  match goal with |- context[data_at ?sh ?t] =>
                 change (data_at(cs := ?cs) sh t) with (field_at_mark cs sh t nil) at 1
                 end;
                 change (data_at_hide ?cs) with (data_at(cs := cs))
 | S ?k => change (data_at(cs := ?cs)) with (data_at_hide cs) at 1;
                find_data_at k
 end.

Definition protect (T: Type) (x: T) := x.
Global Opaque protect.

Section lemmas.

Context `{!VSTGS OK_ty Σ}.

Lemma field_at_ptr_neq {cs: compspecs} :
   forall sh t fld p1 p2 v1 v2,
  sh ≠ Share.bot ->
   0 < sizeof (nested_field_type t (fld :: nil))  ->
   field_at sh t (fld::nil) v1 p1 ∗
   field_at sh t (fld::nil) v2 p2
   ⊢
   ⌜~ ptr_eq p1 p2⌝.
Proof.
   intros.
   apply not_prop_right; intros.
   rewrite -> (ptr_eq_e _ _ H1).
   apply field_at_conflict; try assumption.
Qed.

Lemma field_at_ptr_neq_andp_emp {cs: compspecs} :
    forall sh t fld p1 p2 v1 v2,
  sh ≠ Share.bot ->
 0 < sizeof (nested_field_type t (fld :: nil))  ->
   field_at sh t (fld::nil) v1 p1 ∗
   field_at sh t (fld::nil) v2 p2
   ⊢
   field_at sh t (fld::nil) v1 p1 ∗
   field_at sh t (fld::nil) v2 p2 ∗
   (⌜~ ptr_eq p1 p2⌝ ∧ emp).
Proof.
  intros.
  iIntros "H".
  iDestruct (field_at_ptr_neq with "H") as %?; [done..|].
  iDestruct "H" as "($ & $)"; done.
Qed.

Lemma field_at_ptr_neq_null {cs: compspecs} :
   forall sh t fld v p,
   field_at sh t fld v p ⊢ ⌜~ ptr_eq p nullval⌝.
Proof.
  intros.
  rewrite -> field_at_isptr.
  normalize. apply bi.pure_intro.
  destruct p; unfold nullval; simpl in *; tauto.
Qed.

Lemma spacer_share_join:
  forall sh1 sh2 sh J K q,
   sepalg.join sh1 sh2 sh ->
   spacer sh1 J K q ∗ spacer sh2 J K q ⊣⊢ spacer sh J K q.
Proof.
  intros.
  unfold spacer.
  if_tac. { apply bi.sep_emp. }
  unfold at_offset.
  apply memory_block_share_join; auto.
Qed.

Lemma struct_pred_cons2:
  forall it it' m (A: member -> Type)
   (P: forall it, A it -> val -> mpred)
   (v: compact_prod (map A (it::it'::m)))
   (p: val),
 struct_pred (it :: it' :: m) P v p =
    (P _ (fst v) p ∗ struct_pred (it'::m) P (snd v) p).
Proof.
intros.
destruct v; reflexivity.
Qed.

Lemma union_pred_cons2:
  forall it it' m (A: member -> Type)
   (P: forall it, A it -> val -> mpred)
   (v: compact_sum (map A (it::it'::m)))
   (p: val),
 union_pred (it :: it' :: m) P v p =
   match v with inl v => P _ v p | inr v => union_pred (it'::m) P v p end.
Proof.
intros.
destruct v; reflexivity.
Qed.

Lemma struct_pred_timeless: forall m {A} (P : forall it : member, A it -> val -> mpred) v p
  (HP : forall it a p, (P it a p = emp) \/ Timeless (P it a p)),
  (struct_pred m P v p = emp) \/ Timeless (struct_pred m P v p).
Proof.
  intros.
  induction m as [| a1 m]; intros; auto.
  destruct m; eauto.
  rewrite struct_pred_cons2.
  destruct (HP a1 v.1 p) as [Hemp | Htimeless], (IHm v.2) as [Hemp' | Htimeless'].
  - left; rewrite Hemp, Hemp'; apply sep_emp.
  - right; rewrite Hemp, emp_sep; done.
  - right; rewrite Hemp', sep_emp; done.
  - right; apply _.
Qed.

Lemma spacer_timeless : forall sh a b p, b - a > 0 -> Timeless (spacer sh a b p).
Proof.
  intros; unfold spacer.
  rewrite if_false by lia.
  by apply memory_block_timeless.
Qed.

Lemma withspacer_timeless : forall sh a b P p, a <= b -> Timeless (P p) -> Timeless (withspacer sh a b P p).
Proof.
  intros; unfold withspacer.
  if_tac; last apply bi.sep_timeless; try apply _.
  apply spacer_timeless; lia.
Qed.

Lemma data_at_rec_timeless {cs:compspecs} (sh : share) t (v : reptype t) p : sizeof t > 0 -> Timeless (data_at_rec sh t v p).
Proof.
  revert v p.
  type_induction t; intros; rewrite data_at_rec_eq; try apply _;
    try (simple_if_tac; [by apply memory_block_timeless | apply _]).
  - simpl in *.
    unfold array_pred, aggregate_pred.array_pred.
    apply bi.and_timeless; first apply _.
    rewrite Z.sub_0_r, Z.max_r by lia.
    assert (Ctypes.sizeof t > 0) by lia.
    set (lo := 0).
    assert (lo >= 0) by lia.
    assert (Z.to_nat z > 0) as Hz by lia; clear H.
    forget (Z.to_nat z) as n; clearbody lo.
    match goal with |-context[aggregate_pred.rangespec _ _ ?Q] => set (P := Q) end.
    assert (forall i v, Timeless (P i v)).
    { intros; apply IH; auto. }
    clearbody P; clear IH; generalize dependent lo; induction n; first lia; simpl; intros.
    destruct (eq_dec n O).
    + subst; simpl. eapply bi.Timeless_proper; first apply bi.sep_emp.
      apply _.
    + apply bi.sep_timeless; try apply _.
      apply IHn; lia.
  - edestruct struct_pred_timeless; last done.
    + intros.
      destruct (Z.gt_dec (sizeof (field_type (name_member it) (co_members (get_co id)))) 0).
      * right; apply withspacer_timeless.
        {
Abort.

(*Lemma data_at_timeless {cs:compspecs} sh t v p : sizeof t > 0 -> Timeless (data_at sh t v p).
Proof.
  intros.
  apply bi.and_timeless; first apply _.
  by apply data_at_rec_timeless.
Qed.*)

Lemma data_at_rec_void:
  forall {cs: compspecs}
      sh t v q, t = Tvoid -> data_at_rec sh t v q = False.
Proof.
 intros; subst; reflexivity.
Qed.

Lemma field_at_share_join {cs: compspecs}:
  forall sh1 sh2 sh t gfs v p,
    sepalg.join sh1 sh2 sh ->
   field_at sh1 t gfs v p ∗ field_at sh2 t gfs v p ⊣⊢ field_at sh t gfs v p.
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

Lemma field_at__share_join {cs: compspecs}:
  forall sh1 sh2 sh t gfs p,
    sepalg.join sh1 sh2 sh ->
   field_at_ sh1 t gfs p ∗ field_at_ sh2 t gfs p ⊣⊢ field_at_ sh t gfs p.
Proof. intros. apply field_at_share_join. auto. Qed.

Lemma data_at_share_join {cs: compspecs}:
  forall sh1 sh2 sh t v p,
    sepalg.join sh1 sh2 sh ->
   data_at sh1 t v p ∗ data_at sh2 t v p ⊣⊢ data_at sh t v p.
Proof. intros. apply field_at_share_join; auto. Qed.

Lemma data_at__share_join {cs: compspecs}:
  forall sh1 sh2 sh t p,
    sepalg.join sh1 sh2 sh ->
   data_at_ sh1 t p ∗ data_at_ sh2 t p ⊣⊢ data_at_ sh t p.
Proof. intros. apply data_at_share_join; auto. Qed.

Lemma data_at_conflict_glb: forall {cs: compspecs} sh1 sh2 t v v' p,
  sepalg.nonidentity (Share.glb sh1 sh2) ->
  0 < sizeof t ->
  data_at sh1 t v p ∗ data_at sh2 t v' p ⊢ False.
Proof.
  intros.
  pose (sh := Share.glb sh1 sh2).
  assert (sepalg.join sh (Share.glb sh1 (Share.comp sh)) sh1). {
    hnf. rewrite (Share.glb_commute sh1), <- Share.glb_assoc, Share.comp2.
     rewrite Share.glb_commute, Share.glb_bot.
     split; auto. 
     rewrite Share.distrib2, Share.comp1.
      rewrite Share.glb_commute, Share.glb_top.
      unfold sh. rewrite Share.lub_commute, Share.lub_absorb. auto.
   }
  assert (sepalg.join sh (Share.glb sh2 (Share.comp sh)) sh2). {
    hnf. rewrite (Share.glb_commute sh2), <- Share.glb_assoc, Share.comp2.
     rewrite Share.glb_commute, Share.glb_bot.
     split; auto. 
     rewrite Share.distrib2, Share.comp1.
      rewrite Share.glb_commute, Share.glb_top.
      unfold sh. rewrite Share.glb_commute.
     rewrite Share.lub_commute, Share.lub_absorb. auto.
   }
  rewrite <- (data_at_share_join _ _ _ _ _ _ H1).
  rewrite <- (data_at_share_join _ _ _ _ _ _ H2).
  iIntros "((H11 & H12) & (H21 & H22))".
  iDestruct (data_at_conflict with "[$H11 $H21]") as "[]"; auto.
Qed.

Lemma nonreadable_memory_block_field_at:
  forall  {cs: compspecs}
      sh t gfs v p,
  ~ readable_share sh ->
   value_fits _ v ->
   memory_block sh (sizeof (nested_field_type t gfs)) (field_address t gfs p) ⊣⊢ field_at sh t gfs v p.
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
    rewrite (Z.mod_small ofs) in * by lia.
    pose proof Zmod_le (ofs + nested_field_offset t gfs) Ptrofs.modulus.
    spec H2; [pose proof Ptrofs.modulus_pos; lia |].
    revert H; solve_mod_modulus; intros.
    rewrite Zmod_small in H by (pose proof sizeof_pos (nested_field_type t gfs); lia).
    apply nonreadable_memory_block_data_at_rec; try tauto; try lia.
  + unfold field_at_, field_at.
    rewrite memory_block_isptr.
    apply bi.equiv_entails_2; normalize.
Qed.

Lemma nonreadable_memory_block_data_at: forall {cs: compspecs} sh t v p,
  ~ readable_share sh ->
  field_compatible t nil p ->
  value_fits t v ->
  memory_block sh (sizeof t) p ⊣⊢ data_at sh t v p.
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
   field_at sh t gfs v p ⊣⊢ field_at sh t gfs v' p.
Proof.
intros.
rewrite !field_at_data_at.
apply bi.equiv_entails_2; saturate_local.
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
   memory_block ash (sizeof t) p ∗ data_at bsh t v p ⊣⊢ data_at psh t v p.
Proof.
intros.
apply bi.equiv_entails_2; saturate_local.
rewrite @nonreadable_memory_block_data_at with (v:=v); auto.
unfold data_at.
erewrite field_at_share_join; eauto.
rewrite @nonreadable_memory_block_data_at with (v:=v); auto.
unfold data_at.
erewrite field_at_share_join; eauto.
Qed.

Lemma nonreadable_data_at_eq {cs: compspecs}:
  forall sh t v v' p, ~readable_share sh ->
   (value_fits t v <-> value_fits t v') ->
     data_at sh t v p ⊣⊢ data_at sh t v' p.
Proof.
intros.
unfold data_at.
apply nonreadable_field_at_eq; auto.
Qed.

Lemma field_at_share_join_W {cs: compspecs}:
  forall sh1 sh2 sh t gfs v1 v2 p,
    sepalg.join sh1 sh2 sh ->
    writable_share sh1 ->
    field_at sh1 t gfs v1 p ∗ field_at sh2 t gfs v2 p ⊢ field_at sh t gfs v1 p.
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
    data_at sh1 t v1 p ∗ data_at sh2 t v2 p ⊢ data_at sh t v1 p.
Proof.
  intros.
  apply field_at_share_join_W; auto.
Qed.

Lemma value_fits_Tint_trivial {cs: compspecs} :
  forall s a  i, value_fits (Tint I32 s a) (Vint i).
Proof.
intros.
rewrite value_fits_eq; simpl.
unfold type_is_volatile; simpl.
destruct (attr_volatile a); auto.
hnf. intro. apply Coq.Init.Logic.I.
Qed.

(* TODO: move all change type lemmas into one file. Also those change compspecs lemmas. *)
Lemma data_at_tuint_tint {cs: compspecs}: forall sh v p, data_at sh tuint v p = data_at sh tint v p.
Proof.
  intros.
  unfold data_at, field_at.
  f_equal.
  f_equal; apply prop_ext.
  unfold field_compatible.
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
  f_equiv; auto.
  apply field_compatible_field_address; auto.
Qed.

Lemma mapsto_field_at_ramify {cs: compspecs} sh t gfs v v' w w' p:
  type_is_by_value (nested_field_type t gfs) = true ->
  type_is_volatile (nested_field_type t gfs) = false ->
  JMeq v v' ->
  JMeq w w' ->
  field_at sh t gfs v' p ⊢
    mapsto sh (nested_field_type t gfs) (field_address t gfs p) v ∗
     (mapsto sh (nested_field_type t gfs) (field_address t gfs p) w -∗
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
  iIntros "$ $".
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
  f_equiv; auto.
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
  f_equiv; auto.
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
  data_at (cs := cs) sh t1 v1 = data_at sh t2 v2.
Proof. intros. subst. apply JMeq_eq in H0. subst v2. reflexivity. Qed.

Lemma field_at_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) gfs v1 v2 p,
  JMeq v1 v2 ->
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  field_at (cs := cs_from) sh t gfs v1 p ⊣⊢ field_at (cs := cs_to) sh t gfs v2 p.
Proof.
  intros.
  unfold field_at.
  apply andp_prop_ext.
  + apply field_compatible_change_composite; auto.
  + intros.
    pose proof H1.
    rewrite field_compatible_change_composite in H2 by auto.
    rewrite nested_field_offset_change_composite by auto.
    revert v1 H; rewrite nested_field_type_change_composite by auto.
    intros.
    apply data_at_rec_change_composite; auto.
    apply nested_field_type_preserves_change_composite; auto.
Qed.

Lemma field_at__change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) gfs p,
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  field_at_ (cs := cs_from) sh t gfs p ⊣⊢ field_at_ (cs := cs_to) sh t gfs p.
Proof.
  intros.
  apply field_at_change_composite; auto.
  rewrite nested_field_type_change_composite by auto.
  apply default_val_change_composite.
  apply nested_field_type_preserves_change_composite; auto.
Qed.

Lemma data_at_change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) v1 v2 p,
  JMeq v1 v2 ->
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  data_at (cs := cs_from) sh t v1 p ⊣⊢ data_at (cs := cs_to) sh t v2 p.
Proof.
  intros.
  apply field_at_change_composite; auto.
Qed.

Lemma data_at__change_composite {cs_from cs_to} {CCE: change_composite_env cs_from cs_to}: forall (sh: Share.t) (t: type) p,
  cs_preserve_type cs_from cs_to (coeq _ _) t = true ->
  data_at_ (cs := cs_from) sh t p ⊣⊢ data_at_ (cs := cs_to) sh t p.
Proof.
  intros.
  apply field_at__change_composite; auto.
Qed.

(* TODO: rename and clean up all array_at_data_at lemmas. *)
Lemma array_at_data_at1 {cs : compspecs} : forall sh t gfs lo hi v p,
   lo <= hi ->
   field_compatible0 t (gfs SUB lo) p ->
   field_compatible0 t (gfs SUB hi) p ->
  array_at sh t gfs lo hi v p =
  at_offset (data_at sh (nested_field_array_type t gfs lo hi) v)
               (nested_field_offset t (ArraySubsc lo :: gfs)) p.
Proof.
  intros. rewrite array_at_data_at by auto. unfold at_offset.
  normalize.
Qed.

Lemma data_at_ext_derives {cs : compspecs} sh t v v' p q: v=v' -> p=q -> data_at sh t v p ⊢ data_at sh t v' q.
Proof. intros; subst.
apply derives_refl.
Qed.

Lemma data_at_ext_eq {cs : compspecs} sh t v v' p q: v=v' -> p=q -> data_at sh t v p = data_at sh t v' q.
Proof. intros; subst. trivial. Qed.

End lemmas.

(* does not simplify array indices, because that might be too expensive *)
Ltac simpl_compute_legal_nested_field :=
  repeat match goal with
  | |- context [ compute_legal_nested_field ?T ?L ] =>
    let r := eval hnf in (compute_legal_nested_field T L) in
    change (compute_legal_nested_field T L) with r
  end.

Ltac solve_legal_nested_field_in_entailment :=
   match goal with
   | |- _ ⊢ ⌜legal_nested_field ?t_root ?gfs⌝ =>
     try unfold t_root;
     try unfold gfs;
     try match gfs with
     | (?gfs1 ++ ?gfs0) => try unfold gfs1; try unfold gfs0
     end
  end;
  first
  [ apply bi.pure_intro; apply compute_legal_nested_field_spec';
    simpl_compute_legal_nested_field;
    repeat apply Forall_cons; try apply Forall_nil; lia
  |
  apply compute_legal_nested_field_spec;
  simpl_compute_legal_nested_field;
  repeat apply Forall_cons; try apply Forall_nil;
  try solve [apply bi.pure_intro; auto; lia];
  try solve [normalize; apply bi.pure_intro; auto; lia]
  ].

Ltac headptr_field_compatible :=
  match goal with H: headptr ?P |- field_compatible _ _ ?P =>
  apply headptr_field_compatible;
        [ apply H | reflexivity | | simpl; computable | apply la_env_cs_sound; reflexivity];
    apply compute_legal_nested_field_spec';
    simpl_compute_legal_nested_field;
    repeat apply Forall_cons; try apply Forall_nil
  end.

#[export] Hint Extern 2 (field_compatible _ _ _) => headptr_field_compatible : field_compatible.

(* BEGIN New experiments *)
Section new_lemmas.

Context `{!VSTGS OK_ty Σ}.

Lemma data_at_data_at_cancel  {cs: compspecs}: forall sh t v v' p,
  v = v' ->
  data_at sh t v p ⊢ data_at sh t v' p.
Proof. intros. subst. apply derives_refl. Qed.

Lemma field_at_field_at_cancel  {cs: compspecs}: forall sh t gfs v v' p,
  v = v' ->
  field_at sh t gfs v p ⊢ field_at sh t gfs v' p.
Proof. intros. subst. apply derives_refl. Qed.

Lemma data_at__data_at {cs: compspecs}:
   forall sh t v p, v = default_val t -> data_at_ sh t p ⊢ data_at sh t v p.
Proof.
intros; subst; unfold data_at_; apply derives_refl.
Qed.

Lemma data_at__eq : forall {cs : compspecs} sh t p, data_at_ sh t p = data_at sh t (default_val t) p.
Proof.
  intros; unfold data_at_, data_at, field_at_; auto.
Qed.

Lemma data_at_shares_join : forall {cs : compspecs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh),
  data_at sh1 t v p ∗ ([∗ list] sh ∈ shs, data_at sh t v p) ⊣⊢
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    apply bi.sep_emp.
  - inv Hsplit.
    rewrite assoc, data_at_share_join; eauto; apply _.
Qed.

Lemma data_at_shares_join_old : forall {cs : compspecs} sh t v p shs sh1 (Hsplit : sepalg_list.list_join sh1 shs sh),
  data_at sh1 t v p ∗ fold_right bi_sep emp (map (fun sh => data_at sh t v p) shs) ⊣⊢
  data_at sh t v p.
Proof.
  induction shs; intros; simpl.
  - inv Hsplit.
    apply bi.sep_emp.
  - inv Hsplit.
    rewrite assoc, data_at_share_join; eauto; apply _.
Qed.

Lemma struct_pred_value_cohere : forall {cs : compspecs} m sh1 sh2 p t f off v1 v2
  (Hsh1 : readable_share sh1) (Hsh2 : readable_share sh2)
  (IH : Forall (fun it : member => forall v1 v2 (p : val),
        readable_share sh1 -> readable_share sh2 ->
        data_at_rec sh1 (t it) v1 p ∗ data_at_rec sh2 (t it) v2 p ⊢
        data_at_rec sh1 (t it) v1 p ∗ data_at_rec sh2 (t it) v1 p) m),
  struct_pred m (fun (it : member) v =>
    withspacer sh1 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh1 (t it) v) (f it))) v1 p ∗
  struct_pred m (fun (it : member) v =>
    withspacer sh2 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh2 (t it) v) (f it))) v2 p ⊢
  struct_pred m (fun (it : member) v =>
    withspacer sh1 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh1 (t it) v) (f it))) v1 p ∗
  struct_pred m (fun (it : member) v =>
    withspacer sh2 (f it + sizeof (t it)) (off it) (at_offset (data_at_rec sh2 (t it) v) (f it))) v1 p.
Proof.
  intros.
  revert v1 v2; induction m; auto; intros.
  inv IH.
  destruct m.
  - unfold withspacer, at_offset; simpl.
    if_tac; auto.
    match goal with |- (?P1 ∗ ?Q1) ∗ (?P2 ∗ ?Q2) ⊢ _ => trans ((P1 ∗ P2) ∗ (Q1 ∗ Q2));
      [cancel|] end.
    rewrite H1; auto.
    cancel.
  - rewrite !struct_pred_cons2.
    match goal with |- (?P1 ∗ ?Q1) ∗ (?P2 ∗ ?Q2) ⊢ _ => trans ((P1 ∗ P2) ∗ (Q1 ∗ Q2));
      [cancel|] end.
    match goal with |- _ ⊢ (?P1 ∗ ?Q1) ∗ (?P2 ∗ ?Q2) => trans ((P1 ∗ P2) ∗ (Q1 ∗ Q2));
      [|cancel] end.
    apply bi.sep_mono; auto.
    unfold withspacer, at_offset; simpl.
    if_tac; auto.
    match goal with |- (?P1 ∗ ?Q1) ∗ (?P2 ∗ ?Q2) ⊢ _ => trans ((P1 ∗ P2) ∗ (Q1 ∗ Q2));
      [cancel|] end.
    rewrite H1; auto.
    cancel.
Qed.

Lemma mapsto_value_eq: forall sh1 sh2 t p v1 v2, readable_share sh1 -> readable_share sh2 ->
  v1 <> Vundef -> v2 <> Vundef -> mapsto sh1 t p v1 ∗ mapsto sh2 t p v2 ⊢ ⌜v1 = v2⌝.
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try solve [iIntros "([] & _)"].
  destruct (type_is_volatile t); try solve [iIntros "([] & _)"].
  destruct p; try solve [iIntros "([] & _)"].
  rewrite !if_true by done.
  iIntros "([(_ & H1) | (-> & % & H1)] & [(_ & H2) | (-> & % & H2)])"; try solve [exfalso; pose proof (JMeq_refl Vundef); done];
    iApply res_predicates.address_mapsto_value_cohere; iFrame.
Qed.

Lemma mapsto_value_cohere: forall sh1 sh2 t p v1 v2, readable_share sh1 ->
  mapsto sh1 t p v1 ∗ mapsto sh2 t p v2 ⊢ mapsto sh1 t p v1 ∗ mapsto sh2 t p v1.
Proof.
  intros; unfold mapsto.
  destruct (access_mode t); try simple apply derives_refl.
  destruct (type_is_volatile t); try simple apply derives_refl.
  destruct p; try simple apply derives_refl.
  rewrite if_true by done.
  destruct (eq_dec v1 Vundef).
  - subst; rewrite !prop_false_andp with (P := tc_val t Vundef), !bi.False_or, prop_true_andp; auto;
      try apply tc_val_Vundef.
    cancel.
    if_tac.
    + iIntros "[(% & ?) | (% & ?)]"; iRight; auto.
    + Intros. iIntros "$"; iPureIntro; repeat split; auto. apply tc_val'_Vundef.
  - rewrite !prop_false_andp with (P := v1 = Vundef), !bi.or_False; auto; Intros.
    apply bi.and_intro; [apply bi.pure_intro; auto|].
    if_tac.
    + iIntros "(H1 & H2)".
      iAssert (∃ v2' : val, res_predicates.address_mapsto m v2' _ _) with "[H2]" as (v2') "H2".
      { iDestruct "H2" as "[(% & ?) | (_ & $)]"; auto. }
      iAssert ⌜v1 = v2'⌝ as %->. { iApply res_predicates.address_mapsto_value_cohere; iFrame. }
      iFrame; eauto.
    + apply bi.sep_mono; first done.
      iIntros "((% & %) & $)"; iPureIntro; repeat split; auto.
      apply tc_val_tc_val'; auto.
Qed.

Lemma data_at_value_cohere : forall {cs : compspecs} sh1 sh2 t v1 v2 p, readable_share sh1 ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 t v1 p ∗ data_at sh2 t v2 p ⊢
  data_at sh1 t v1 p ∗ data_at sh2 t v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset.
  iIntros "((% & ?) & (% & ?))".
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  iDestruct (mapsto_value_cohere with "[-]") as "($ & $)"; auto; iFrame.
Qed.

Lemma data_at_value_eq : forall {cs : compspecs} sh1 sh2 t v1 v2 p,
  readable_share sh1 -> readable_share sh2 ->
  is_pointer_or_null v1 -> is_pointer_or_null v2 ->
  data_at sh1 (tptr t) v1 p ∗ data_at sh2 (tptr t) v2 p ⊢ ⌜v1 = v2⌝.
Proof.
  intros; unfold data_at, field_at, at_offset; Intros.
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  apply mapsto_value_eq; auto.
  { intros X; subst; contradiction. }
  { intros X; subst; contradiction. }
Qed.

Lemma data_at_array_value_cohere : forall {cs : compspecs} sh1 sh2 t z a v1 v2 p, readable_share sh1 ->
  type_is_by_value t = true -> type_is_volatile t = false ->
  data_at sh1 (Tarray t z a) v1 p ∗ data_at sh2 (Tarray t z a) v2 p ⊢
  data_at sh1 (Tarray t z a) v1 p ∗ data_at sh2 (Tarray t z a) v1 p.
Proof.
  intros; unfold data_at, field_at, at_offset.
  iIntros "((% & H1) & (_ & H2))".
  rewrite !bi.pure_True, !bi.True_and by done.
  rewrite !data_at_rec_eq; simpl.
  unfold array_pred, aggregate_pred.array_pred.
  iDestruct "H1" as (?) "H1"; iDestruct "H2" as (?) "H2".
  rewrite !bi.pure_True, !bi.True_and by done.
  rewrite Z.sub_0_r in *.
  rewrite Z2Nat_max0 in *.
  clear H3 H4.
  forget (offset_val 0 p) as p'; forget (Z.to_nat z) as n.
  set (lo := 0) at 1 3 5 7; clearbody lo.
  iInduction n as [|] "IH" forall (lo); auto; simpl; intros.
  iDestruct "H1" as "(H1a & H1b)"; iDestruct "H2" as "(H2a & H2b)".
  unfold at_offset.
  rewrite !by_value_data_at_rec_nonvolatile by auto.
  iDestruct (mapsto_value_cohere with "[$H1a $H2a]") as "($ & $)"; first done.
  iApply ("IH" with "H1b H2b").
Qed.

Lemma field_at_array_inbounds : forall {cs : compspecs} sh t z a i v p,
  field_at sh (Tarray t z a) (ArraySubsc i :: nil) v p ⊢ ⌜0 <= i < z⌝.
Proof.
  intros. rewrite field_at_compatible'.
  apply bi.pure_elim_l. intros.
  apply bi.pure_intro.
  destruct H as (_ & _ & _ & _ & _ & ?); auto.
Qed.

Lemma field_at__field_at {cs: compspecs} :
   forall sh t gfs v p, v = default_val (nested_field_type t gfs) -> field_at_ sh t gfs p ⊢ field_at sh t gfs v p.
Proof.
intros; subst; unfold field_at_; apply derives_refl.
Qed.

Lemma data_at__field_at {cs: compspecs}:
   forall sh t v p, v = default_val t -> data_at_ sh t p ⊢ field_at sh t nil v p.
Proof.
intros; subst; unfold data_at_; apply derives_refl.
Qed.

Lemma field_at__data_at {cs: compspecs} :
   forall sh t v p, v = default_val (nested_field_type t nil) -> field_at_ sh t nil p ⊢ data_at sh t v p.
Proof.
intros; subst; unfold field_at_; apply derives_refl.
Qed.

Lemma field_at_data_at_cancel': forall {cs : compspecs} sh t v p,
  field_at sh t nil v p = data_at sh t v p.
Proof.
  intros. reflexivity.
Qed.

End new_lemmas.

#[export] Hint Resolve data_at_data_at_cancel : cancel.
#[export] Hint Resolve data_at_data_at_cancel : cancel.
#[export] Hint Resolve field_at_field_at_cancel : cancel.
#[export] Hint Resolve data_at__data_at : cancel.
#[export] Hint Resolve field_at__field_at : cancel.
#[export] Hint Resolve data_at__field_at : cancel.
#[export] Hint Resolve field_at__data_at : cancel.

#[export] Hint Extern 1 (_ = @default_val _ _) =>
 match goal with |- ?A = ?B =>
     let x := fresh "x" in set (x := B); hnf in x; subst x;
     match goal with |- ?A = ?B => constr_eq A B; reflexivity
  end end : core.

#[export] Hint Extern 1 (_ = _) =>
  match goal with |- ?A = ?B => constr_eq A B; reflexivity end : cancel.

(* enhance cancel to solve field_at and data_at *)

#[export] Hint Rewrite
  @field_at_data_at_cancel'
  @field_at_data_at
  @field_at__data_at_ : cancel.
 
(* END new experiments *)

Section more_lemmas.

Context `{!VSTGS OK_ty Σ}.

Lemma data_at__Tarray:
  forall {CS: compspecs} sh t n a,
  data_at_ sh (Tarray t n a) =
  data_at sh (Tarray t n a) (Zrepeat (default_val t) n).
Proof. reflexivity. Qed.

Lemma data_at__tarray:
  forall {CS: compspecs} sh t n,
  data_at_ sh (tarray t n) =
  data_at sh (tarray t n) (Zrepeat (default_val t) n).
Proof. intros; apply data_at__Tarray; auto. Qed.

Lemma data_at__Tarray':
  forall {CS: compspecs} sh t n a v,
  v = Zrepeat (default_val t) n ->
  data_at_ sh (Tarray t n a) = data_at sh (Tarray t n a) v.
Proof.
intros. subst; reflexivity.
Qed.

Lemma data_at__tarray':
  forall {CS: compspecs} sh t n v,
  v = Zrepeat (default_val t) n ->
  data_at_ sh (tarray t n) = data_at sh (tarray t n) v.
Proof. intros; apply data_at__Tarray'; auto. Qed.

Lemma change_compspecs_field_at_cancel:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type) gfs
        (v1: @reptype cs1 (@nested_field_type cs1 t1 gfs))
        (v2: @reptype cs2 (@nested_field_type cs2 t2 gfs))
        (p: val),
    t1 = t2 ->
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   JMeq v1 v2 ->
   field_at (cs := cs1) sh t1 gfs v1 p ⊢ field_at (cs := cs2) sh t2 gfs v2 p.
Proof.
intros.
subst t2.
rewrite @field_at_change_composite with CCE; auto.
Qed.

Lemma change_compspecs_data_at_cancel:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type)
        (v1: @reptype cs1 t1) (v2: @reptype cs2 t2)
        (p: val),
    t1 = t2 ->
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   JMeq v1 v2 ->
   data_at (cs := cs1) sh t1 v1 p ⊢ data_at (cs := cs2) sh t2 v2 p.
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
   field_at_ (cs := cs1) sh t1 gfs p ⊢ field_at_ (cs := cs2) sh t2 gfs p.
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
   data_at_ (cs := cs1) sh t1 p ⊢ data_at_ (cs := cs2) sh t2 p.
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
   field_at (cs := cs1) sh t1 gfs v1 p ⊢ field_at_ (cs := cs2) sh t2 gfs p.
Proof.
intros.
subst t2.
rewrite field_at_field_at_.
apply @change_compspecs_field_at_cancel2 with CCE; auto.
Qed.

Lemma change_compspecs_data_at_cancel3:
  forall {cs1 cs2: compspecs} {CCE : change_composite_env cs1 cs2}
        (sh: share) (t1 t2: type)
        (v1: @reptype cs1 t1)
        (p: val),
    t1 = t2 ->
    cs_preserve_type cs1 cs2 (@coeq cs1 cs2 CCE) t1 = true ->
   data_at (cs := cs1) sh t1 v1 p ⊢ data_at_ (cs := cs2) sh t2 p.
Proof.
intros.
apply @change_compspecs_field_at_cancel3 with CCE; auto.
Qed.

Lemma data_at_nullptr:
 forall {cs: compspecs} sh t p,
  data_at sh size_t nullval p ⊣⊢
  data_at sh (tptr t) nullval p.
Proof.
intros.
unfold data_at, field_at.
apply bi.and_proper.
f_equiv.
unfold field_compatible; simpl.
intuition; destruct p; try auto;
(eapply align_compatible_rec_by_value_inv in H2; [ | reflexivity];
 eapply align_compatible_rec_by_value; [reflexivity | ];
 apply H2).
unfold at_offset.
rewrite !by_value_data_at_rec_nonvolatile by reflexivity.
simpl.
unfold nested_field_type; simpl.
rewrite <- mapsto_tuint_tptr_nullval with (t:=t).
done.
Qed.

Lemma data_at_int_or_ptr_int:
 forall {CS: compspecs} sh i p,
  data_at sh int_or_ptr_type (Vptrofs i) p
  = data_at sh size_t (Vptrofs i) p.
Proof.
 intros.
 unfold data_at, field_at.
 simpl. f_equal.
 f_equal.
 unfold field_compatible.
 f_equal.
 f_equal.
 f_equal.
 f_equal.
 unfold align_compatible.
 destruct p; auto.
 apply prop_ext; split; intro;
  eapply align_compatible_rec_by_value_inv in H;
   try reflexivity;
  try (eapply align_compatible_rec_by_value; eauto).
Qed.

Lemma data_at_int_or_ptr_ptr:
 forall {CS: compspecs} sh t v p,
  isptr v ->
  data_at sh int_or_ptr_type v p
  = data_at sh (tptr t) v p.
Proof.
 intros.
 destruct v; try contradiction.
 clear H.
 unfold data_at, field_at.
 simpl. f_equal.
 f_equal.
 unfold field_compatible.
 f_equal.
 f_equal.
 f_equal.
 f_equal.
 unfold align_compatible.
 destruct p; auto.
 apply prop_ext; split; intro;
  eapply align_compatible_rec_by_value_inv in H;
   try reflexivity;
  try (eapply align_compatible_rec_by_value; eauto).
 unfold at_offset.
 unfold nested_field_type;  simpl.
 unfold data_at_rec; simpl.
 unfold mapsto.
 simpl.
 destruct p; simpl; auto.
 if_tac; auto.
 f_equal.
 simple_if_tac; auto.
 f_equal. rewrite andb_false_r. reflexivity.
 f_equal. rewrite andb_false_r. reflexivity.
 f_equal.
 f_equal.
 f_equal.
 unfold tc_val'.
 unfold tc_val; simpl.
 rewrite N.eqb_refl.
 rewrite andb_false_r. reflexivity.
Qed.

Lemma nonempty_writable0_glb (shw shr : share) : writable0_share shw -> readable_share shr ->
  nonempty_share (Share.glb shw shr).
 (* this lemma might be convenient for users *)
Proof.
intros Hshw Hshr.
apply leq_join_sub in Hshw.
apply Share.ord_spec2 in Hshw.
rewrite Share.glb_commute, <- Hshw, Share.distrib1, Share.glb_commute, Share.lub_commute.
apply readable_nonidentity.
apply readable_share_lub.
apply readable_glb.
assumption.
Qed.

Lemma nonempty_writable_glb (shw shr : share) : writable_share shw -> readable_share shr ->
  nonempty_share (Share.glb shw shr).
 (* this lemma might be convenient for users *)
Proof.
intros Hshw Hshr.
apply nonempty_writable0_glb; try assumption.
apply writable_writable0; assumption.
Qed.

End more_lemmas.

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

#[export] Hint Extern 2 (data_at_(cs := ?cs1) ?sh _ ?p ⊢ data_at_(cs := ?cs2) ?sh _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_data_at_cancel2; reflexivity) : cancel.

#[export] Hint Extern 2 (data_at(cs := ?cs1) ?sh _ _ ?p ⊢ data_at_(cs := ?cs2) ?sh _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_data_at_cancel3; reflexivity) : cancel.

#[export] Hint Extern 2 (data_at(cs := ?cs1) ?sh _ _ ?p ⊢ data_at(cs := ?cs2) ?sh _ _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_data_at_cancel;
       [ reflexivity | reflexivity | apply JMeq_refl]) : cancel.

#[export] Hint Extern 2 (field_at_(cs := ?cs1) ?sh _ ?gfs ?p ⊢ field_at_(cs := ?cs2) ?sh _ ?gfs ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_field_at_cancel2; reflexivity) : cancel.

#[export] Hint Extern 2 (field_at(cs := ?cs1) ?sh _ ?gfs _ ?p ⊢ field_at_(cs := ?cs2) ?sh _ ?gfs ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_field_at_cancel3; reflexivity) : cancel.

#[export] Hint Extern 2 (field_at(cs := ?cs1) ?sh _ ?gfs _ ?p ⊢ field_at(cs := ?cs2) ?sh _ ?gfs _ ?p) =>
    (tryif constr_eq cs1 cs2 then fail
     else simple apply change_compspecs_field_at_cancel;
        [ reflexivity | reflexivity | apply JMeq_refl]) : cancel.
