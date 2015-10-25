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
Require Import floyd.sublist.

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
    unfold field_type, fieldlist.field_type2, Ctypes.field_type in H0.
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
      revert H0; unfold field_type, fieldlist.field_type2; simpl.
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
         by (unfold field_type, fieldlist.field_type2; simpl; rewrite if_false; auto).
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

Lemma default_value_fits:
  forall sh t, value_fits sh t (default_val t).
Proof.
  intros.
  type_induction t; try destruct f; rewrite value_fits_ind; 
    unfold tc_val'; simpl;
   try solve [if_tac; auto; if_tac; auto].
  +
simpl.
cbv iota.
rewrite default_val_ind.
rewrite unfold_fold_reptype. 
rewrite Zlength_correct. rewrite length_list_repeat.
split.
destruct (zlt z 0).
rewrite Z2Nat_neg, Z.max_l by omega. reflexivity.
rewrite Z2Nat.id, Z.max_r by omega; reflexivity.
apply Forall_list_repeat.
auto.
+
rewrite default_val_ind.
rewrite unfold_fold_reptype.
assert (NR:= get_co_members_no_replicate id).
apply compute_list_norepet_e in NR.
move IH after NR.
induction (co_members (get_co id)).
apply Coq.Init.Logic.I.
destruct a0 as [i t].
destruct m.
simpl.
inv IH. simpl in *. auto.
inv IH.
destruct p as [i' t'].
inv NR.
specialize (IHm H4). clear H4.
assert (i<>i').
contradict H3. subst; left; auto. clear H3.
rewrite struct_Prop_cons2.
split.
apply H1.
spec IHm.
clear - H2 H. admit.
revert IHm.
apply struct_Prop_ext_derives.
admit.
simpl @fst in *.
intros.
destruct (ident_eq i0 i).
subst i0.
clear H3.
match goal with H: value_fits _ _ ?A |- value_fits _ _ ?B => replace B with A; auto end.
clear - H H0.
unfold struct_default_val.
unfold proj_struct.
admit.
admit.
+
admit.
Qed.

Definition field_at (sh: Share.t) (t: type) (gfs: list gfield) (v: reptype (nested_field_type2 t gfs)) (p: val): mpred :=
 !! (field_compatible t gfs p /\ value_fits (readable_share_dec sh) (nested_field_type2 t gfs) v) 
    && at_offset (data_at' sh (nested_field_type2 t gfs) v) (nested_field_offset2 t gfs) p.
Arguments field_at sh t gfs v p : simpl never.

Definition field_at_ (sh: Share.t) (t: type) (gfs: list gfield) (p: val): mpred :=
  field_at sh t gfs (default_val (nested_field_type2 t gfs)) p.

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
  (v: list (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs)))) (p: val) : mpred :=
  !! (field_compatible0 t (ArraySubsc lo :: gfs) p /\
      field_compatible0 t (ArraySubsc hi :: gfs) p /\
      Zlength v = Z.max 0 (hi-lo) /\
      Forall (value_fits (readable_share_dec sh) (nested_field_type2 t (ArraySubsc 0 :: gfs))) v)
  &&  array_pred  (default_val _) lo hi
    (fun i v => at_offset (data_at' sh (nested_field_type2 t (ArraySubsc 0 :: gfs)) v)
       (nested_field_offset2 t (ArraySubsc i :: gfs))) v p.

Definition array_at_ (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z) : val -> mpred :=
 array_at sh t gfs lo hi (list_repeat (Z.to_nat (hi-lo)) (default_val _)).

(************************************************

field_compatible, local_facts, isptr and offset_zero properties

************************************************)

Lemma field_at_local_facts:
  forall sh t path v c,
     field_at sh t path v c |-- !! (field_compatible t path c /\ value_fits (readable_share_dec sh) (nested_field_type2 t path) v).
Proof.
  intros.
  unfold field_at.
  normalize. autorewrite with subst norm1 norm2; normalize.
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
   forall sh t v p, data_at sh t v p |-- !! (field_compatible t nil p /\ value_fits (readable_share_dec sh) t v).
Proof. intros. apply field_at_local_facts. Qed.

Lemma data_at__local_facts: forall sh t p, data_at_ sh t p |-- !! field_compatible t nil p.
Proof. intros.
  apply field_at__local_facts.
Qed.

Lemma field_compatible_range:
 forall i n t gfs p, 
   0 <= i <= n ->
   field_compatible0 t (ArraySubsc 0 :: gfs) p ->
   field_compatible0 t (ArraySubsc n :: gfs) p ->
   field_compatible0 t (ArraySubsc i :: gfs) p.
Proof.
intros.
destruct H0 as [? [? [? [? [? [? [? [? ?]]]]]]]].
destruct H1 as [? [? [? [? [? [? [? [? ?]]]]]]]].
repeat split; auto.
hnf in H9,H17|-*.
destruct (nested_field_type2 t gfs); auto.
omega.
Qed.

Lemma array_at_local_facts: forall sh t gfs lo hi v p,
  array_at sh t gfs lo hi v p |--
    !! (field_compatible0 t (ArraySubsc lo :: gfs) p 
        /\ field_compatible0 t (ArraySubsc hi :: gfs) p 
        /\ Zlength v = Z.max 0 (hi-lo)
        /\ Forall (value_fits (readable_share_dec sh) (nested_field_type2 t (ArraySubsc 0 :: gfs))) v).
Proof.
  intros.
  unfold array_at.
  apply andp_left1; auto.
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
Proof. intros. apply local_facts_isptr. eapply derives_trans; [ apply field_at_local_facts | normalize]. Qed.

Lemma field_at_offset_zero: forall sh t gfs v p,
  field_at sh t gfs v p = field_at sh t gfs v (offset_val Int.zero p).
Proof. intros. apply local_facts_offset_zero.
 intros. rewrite field_at_isptr; normalize.
Qed.

Lemma field_at__isptr: forall sh t gfs p,
  field_at_ sh t gfs p = (!! isptr p) && field_at_ sh t gfs p.
Proof. intros.
 intros. apply local_facts_isptr.
 eapply derives_trans; [ apply field_at__local_facts | normalize].
Qed.

Lemma field_at__offset_zero: forall sh t gfs p,
  field_at_ sh t gfs p = field_at_ sh t gfs (offset_val Int.zero p).
Proof. intros. apply local_facts_offset_zero.
 intros. rewrite field_at__isptr; normalize.
Qed.

Lemma data_at_isptr: forall sh t v p, data_at sh t v p = !!(isptr p) && data_at sh t v p.
Proof. intros. apply local_facts_isptr.
 eapply derives_trans.
 apply data_at_local_facts.
 normalize.
Qed.

Lemma data_at_offset_zero: forall sh t v p, data_at sh t v p = data_at sh t v (offset_val Int.zero p).
Proof. intros. rewrite <- local_facts_offset_zero. reflexivity.
    intros; rewrite data_at_isptr; normalize.  
Qed.

Lemma data_at__isptr: forall sh t p, data_at_ sh t p = !!(isptr p) && data_at_ sh t p.
Proof. intros.  apply local_facts_isptr.
 eapply derives_trans.
 apply data_at__local_facts.
 normalize.
Qed.

Lemma data_at__offset_zero: forall sh t p, data_at_ sh t p = data_at_ sh t (offset_val Int.zero p).
Proof. intros. apply field_at__offset_zero. Qed.

(************************************************

Ext lemmas of array_at

************************************************)

Lemma array_at_ext_derives: forall sh t gfs lo hi v0 v1 p,
  Zlength v0 = Zlength v1 ->
  (forall i u0 u1,
     lo <= i < hi ->
     JMeq u0 (Znth (i-lo) v0 (default_val _)) ->
     JMeq u1 (Znth (i-lo) v1 (default_val _)) ->
     field_at sh t (ArraySubsc i :: gfs) u0 p |--
     field_at sh t (ArraySubsc i :: gfs) u1 p) -> 
  array_at sh t gfs lo hi v0 p |-- array_at sh t gfs lo hi v1 p.
Proof.
  intros until p. intro ZL; intros.
  unfold array_at, field_at.
   rewrite <- !and_assoc.
   rewrite <- gather_prop_left.
   rewrite <- (gather_prop_left _ (Forall _ _)).
  apply derives_extract_prop; intro G2.
  apply andp_right; [apply prop_right | ].
  destruct G2 as [[? ?] ?]; split; auto. congruence.
  destruct G2 as [[G2 G3] ZL'].
  unfold array_pred, aggregate_pred.array_pred.
  destruct (zlt (hi-lo) 0).
* (* negative case *)
  rewrite Z.max_l in ZL' by omega.
  rewrite Zlength_correct in ZL'; destruct v0; inv ZL'.
  rewrite !Zlength_correct in ZL; destruct v1; inv ZL.
  apply andp_derives.
  apply prop_derives; intros; constructor.
  rewrite Z2Nat_neg by auto. simpl. auto.
* (* nonnegative case *)
  assert (Hg: lo<=hi) by omega; clear g.
  rewrite Z.max_r in ZL' by omega.
  assert (hi = lo + Zlength v0). omega. subst hi. clear ZL'.
  replace (lo + Zlength v0 - lo) with (Zlength v0) by omega.
  remember (Zlength v0) as n. 
  assert (ZL0: length v0 = Z.to_nat n) by admit.
  assert (ZL1: length v1 = Z.to_nat n) by admit.
  rewrite <- (Z2Nat.id n) in H,G3 by admit.
  forget (Z.to_nat n) as n'. clear n Hg Heqn ZL. rename n' into n.
  revert lo G2 G3 v0 v1 ZL0 ZL1 H; induction n; intros.
  simpl. apply andp_derives; auto. apply prop_right. destruct v1; inv ZL1; constructor.
  destruct v0 as [ | x0 v0 ]; inv ZL0.
  destruct v1 as [ | x1 v1 ]; inv ZL1.
  simpl.
  match goal with |- !! Forall ?P _ && (?A * ?A') |-- !! Forall ?P _ && (?B * ?B') =>
     eapply derives_trans; [instantiate (1:= (!! P x0 && A) * (!! Forall P v0 && A')) |
         eapply derives_trans; [instantiate (1:= (!! P x1 && B) * (!! Forall P v1 && B')) | ]]
 end.
  normalize. apply andp_right; auto. inv H0; apply prop_right; split; auto.
 2: normalize; apply andp_right; auto; apply prop_right; constructor; auto.
 apply sepcon_derives.
 specialize (H lo). rewrite Z.sub_diag in H|-*.
 unfold Znth in H|-*. rewrite !if_false in H|-* by omega. rewrite inj_S in H. simpl nth in H|-*.
 assert (exists u0: reptype (nested_field_type2 t (ArraySubsc lo :: gfs)),
             JMeq u0 x0).
 rewrite (nested_field_type2_ArraySubsc t lo gfs). exists x0. reflexivity.
 destruct H0 as [u0 H0].
 assert (exists u1: reptype (nested_field_type2 t (ArraySubsc lo :: gfs)),
             JMeq u1 x1).
 rewrite (nested_field_type2_ArraySubsc t lo gfs). exists x1. reflexivity.
 destruct H2 as [u1 H2].
 specialize (H u0 u1). spec H; [ omega | ].
 specialize (H H0 H2).
 admit.  (* may have to split on cases, (readable_share_dec sh) *)
 clear H.
 specialize (IHn (Z.succ lo)).
 spec IHn.
(*
 clear IHn.
 rewrite field_compatible0_cons in G2, G3 |- *.
    destruct (nested_field_type2 t gfs); try tauto.
    destruct G3 as [G3 ?].
    split; auto. 
    rewrite inj_S in G3; destruct G3; omega.
 specialize (IHn v0 v1 (eq_refl _) H1).
 apply IHn.
 replace (Z
 apply andp_derives. apply prop_derives.
 [ | eapply derives_trans; []

  revert lo v0 v1 ZL0 ZL1 H G2 G3; induction n.
  rewrite <- ZL'. replaceclear ZL' hi.



  apply andp_derives.
   admit.  (* fold this proof into the next subproof, using H *)
  apply array_pred_ext_derives.
  intros.
  generalize (H i).
  unfold  field_at.
  replace (!! (field_compatible t (ArraySubsc i :: gfs) p): mpred) with TT.
  Focus 2. {
    apply ND_prop_ext.
    rewrite field_compatible_cons.
    rewrite field_compatible0_cons in G2, G3.
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
*)
Admitted.

Lemma array_at_ext: forall sh t gfs lo hi v0 v1 p,
  Zlength v0 = Zlength v1 ->
  (forall i u0 u1,
     lo <= i < hi ->
     JMeq u0 (Znth (i-lo) v0 (default_val _)) ->
     JMeq u1 (Znth (i-lo) v1 (default_val _)) ->
     field_at sh t (ArraySubsc i :: gfs) u0 p =
     field_at sh t (ArraySubsc i :: gfs) u1 p) -> 
  array_at sh t gfs lo hi v0 p = array_at sh t gfs lo hi v1 p.
Proof.
  intros.
  apply pred_ext; apply array_at_ext_derives; intros; auto.
  erewrite H0 by eauto; auto.
  erewrite <- H0 by eauto; auto.
Qed.

(*
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
*)

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
   assert (H7:= JMeq_trans (unfold_reptype_JMeq _ v1) H2).
   apply JMeq_eq in H7; subst v2. clear H2.
  f_equal.
  + assert (0 <= 0 <= n /\ 0 <= n <= n) by omega.    
    apply ND_prop_ext; split; intros [? ?].
    rewrite value_fits_ind in H4. destruct H4.
   split3; try tauto.
   split; auto.
   rewrite H4, !Z.max_r by omega. omega.
   split. tauto. destruct H4. destruct H5.
   rewrite value_fits_ind.
   split; auto.
   rewrite Z.max_r in H5|-*; try omega.
  + apply array_pred_ext.
    intros.
    rewrite at_offset_eq.
    rewrite <- at_offset_eq2.
    rewrite !at_offset_eq.
    rewrite (nested_field_offset2_ind t (ArraySubsc i :: gfs))
      by (apply legal_nested_field0_field; simpl; unfold legal_field; rewrite H0; auto).
   rewrite H0. reflexivity.
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

(* Goal forall t gfs p, (!! field_compatible t gfs p) = (!! field_compatible0 t gfs p). *)
(*
Goal forall sh t gfs p, !! field_compatible t gfs (offset_val Int.zero Vundef) && at_offset (memory_block sh Int.zero) 14 (offset_val Int.zero p) = (!! field_compatible0 t gfs p).
intros.
destruct_ptr p.
*)

Lemma data_at_data_at': forall sh t v p,
  data_at sh t v p = !! (field_compatible t nil p /\  value_fits (readable_share_dec sh) (nested_field_type2 t nil) v) && data_at' sh t v p.
Proof.
  intros.
  unfold data_at, field_at.
  apply andp_prop_ext; [reflexivity |].
  intros [? _].
  destruct p; try solve [destruct H; simpl in *; tauto].
  inv_int i.
  rewrite at_offset_eq3.
  rewrite nested_field_offset2_ind, Z.add_0_r by (unfold field_compatible in H; tauto).
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
  rewrite value_fits_ind.
  rewrite at_offset_struct_pred.
  rewrite andp_struct_pred by apply corable_prop.
  generalize (co_members (get_co id)) at 1 11; intro m; destruct m; [auto |].
  apply struct_pred_ext; [apply get_co_members_no_replicate |].
  
  intros.
  rewrite prop_and.
  destruct_ptr p.
  unfold field_at, fst, snd.
  autorewrite with at_offset_db.
  unfold offset_val.
  solve_mod_modulus.
  normalize.
  destruct (legal_nested_field_dec t (StructField i :: gfs)).
  Focus 2. {
    rewrite !prop_and.
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
    assert (value_fits (readable_share_dec sh) (field_type i (co_members (get_co id)))
     (proj_struct i (co_members (get_co id)) (unfold_reptype v1) d0) <-> value_fits (readable_share_dec sh) (nested_field_type2 t (gfs DOT i))
     (proj_struct i (co_members (get_co id)) v2 d1));
     [| rewrite field_compatible_cons, H; tauto].
    apply prop_unext, value_fits_type_changable.
    - rewrite nested_field_type2_ind.
      rewrite H.
      reflexivity.
    - apply (proj_compact_prod_JMeq _ _ (co_members (get_co id)) _ _
        d0 d1 (unfold_reptype v1) v2 member_dec).
      * intros.
        rewrite nested_field_type2_ind, H.
        auto.
      * apply in_members_field_type; auto.
      * rewrite (unfold_reptype_JMeq (Tstruct id a)).
        auto.
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
  rewrite value_fits_ind.
  rewrite at_offset_union_pred.
  rewrite andp_union_pred by apply corable_prop.
  generalize (eq_refl (co_members (get_co id))).
  generalize (co_members (get_co id)) at 2 3 10; intro m; destruct m; [auto |].
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
  rewrite prop_and.
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
    rewrite !prop_and.
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
    assert (value_fits (readable_share_dec sh) (field_type i (co_members (get_co id)))
     (proj_union i (co_members (get_co id)) (unfold_reptype v1) d0) <->
       value_fits (readable_share_dec sh) (nested_field_type2 t (gfs UDOT i))
     (proj_union i (co_members (get_co id)) v2 d1));
    [| rewrite field_compatible_cons, H; tauto].
    apply prop_unext, value_fits_type_changable.
    - rewrite nested_field_type2_ind.
      rewrite H.
      reflexivity.
    - apply (proj_compact_sum_JMeq _ _ (co_members (get_co id)) _ _
        d0 d1 (unfold_reptype v1) v2 member_dec).
      * intros.
        rewrite nested_field_type2_ind, H.
        auto.
      * auto.
      * rewrite (unfold_reptype_JMeq (Tunion id a)).
        auto.
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
  array_at sh t gfs i i v p = !! (field_compatible0 t (ArraySubsc i :: gfs) p /\ v=nil) && emp.
Proof.
  intros.
  unfold array_at.
  rewrite array_pred_len_0 by omega.
  f_equal. f_equal; apply prop_ext; split; intros.
  destruct H as [? [? [? ?]]]. rewrite Zlength_correct, Z.sub_diag in H1.
  destruct v; inv H1. split; auto.
  destruct H. subst v. split3; auto. split; auto. rewrite Z.sub_diag; reflexivity.
Qed.

Lemma array_at_len_1: forall sh t gfs i v v0 p,
  JMeq (Znth 0 v (default_val _)) v0 ->
  array_at sh t gfs i (i + 1) v p = !! (JMeq v (v0::nil)) && field_at sh t (ArraySubsc i :: gfs) v0 p.
Proof.
  intros.
  unfold array_at, field_at. normalize.
  rewrite array_pred_len_1.
  rewrite !at_offset_eq.
  f_equal.
  + rewrite (field_compatible_field_compatible0' t i gfs p).
     replace (i+1-i) with 1 by omega.
      unfold Znth in H. rewrite if_false in H by omega. simpl nth in H.
      assert (HH: nested_field_type2 t (ArraySubsc 0 :: gfs) = nested_field_type2 t (ArraySubsc i :: gfs))
       by (rewrite !nested_field_type2_ind with (gfs0 := _ :: gfs); reflexivity).
      apply ND_prop_ext; split.
      intros [? [? [? ?]]].
      rewrite Zlength_correct in H2.
      change (Z.max 0 1) with (Z.of_nat 1) in H2. apply Nat2Z.inj in H2.
      destruct v; inv H2. destruct v; inv H5. simpl nth in H.
      split3; auto.
      clear - H. forget (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs))) as t1.
      forget (reptype (nested_field_type2 t (ArraySubsc i :: gfs))) as t2.
      inv H. apply JMeq_refl.
      inv H3. clear H6.
      clear - H H5 HH.
      forget (nested_field_type2 t (ArraySubsc 0 :: gfs)) as t1.
      forget (nested_field_type2 t (ArraySubsc i :: gfs)) as t2. subst. apply JMeq_eq in H. subst; auto.
      intros [? [[? ?] ?]].
      split3; auto.
      clear - H0 HH H3.
      forget (nested_field_type2 t (ArraySubsc 0 :: gfs)) as t1.
      forget (nested_field_type2 t (ArraySubsc i :: gfs)) as t2. subst; apply JMeq_eq in H0; subst.
      split. reflexivity. constructor; auto.
  + erewrite data_at'_type_changable; [reflexivity | | auto].
    - rewrite !nested_field_type2_ind with (gfs0 := _ :: gfs).
      destruct (nested_field_type2 t gfs); auto.
Qed.

Lemma split2_array_at: forall sh t gfs lo mid hi v p,
  lo <= mid <= hi ->
  array_at sh t gfs lo hi v p =
  array_at sh t gfs lo mid (sublist 0 (mid-lo) v) p * 
  array_at sh t gfs mid hi (sublist (mid-lo) (Zlength v) v) p.
Proof.
  intros.
  unfold array_at.
  match goal with |- !!(?A /\ ?B /\ ?C /\ ?D) && ?E = 
                             (!!(?A1 /\ ?B1 /\ ?C1 /\ ?D1) && ?E1) * 
                             (!!(?A2 /\ ?B2 /\ ?C2 /\ ?D2) && ?E2) =>
      transitivity (!!(C/\D) && (!!(A/\B) && E));
      [ | transitivity ((!!(C1/\D1) && (!!(A1/\B1) && E1) * (!!(C2/\D2) && (!!(A2/\B2) && E2))))]
 end.
  normalize. f_equal.   apply ND_prop_ext; tauto.
 2: normalize; f_equal; apply ND_prop_ext; tauto.
  normalize.
  apply andp_prop_ext.
*
  split. intros [? [? [? ?]]].
  split3; auto.
  rewrite Z.max_r in H0|-* by omega.
  rewrite Zlength_sublist by omega. omega.
  unfold sublist. simpl skipn. rewrite Z.sub_0_r.
  clear - H1.
  revert v H1; induction (Z.to_nat (mid-lo)); intros. constructor.
  destruct v; inv H1; simpl; constructor; auto.
  split3; auto.
  rewrite field_compatible0_cons with (gfs0 := gfs) in H2,H3.
  destruct (nested_field_type2 t gfs) eqn:?; try contradiction.
  destruct H2, H3.
  rewrite !field_compatible0_cons with (gfs0 := gfs), Heqt0.
  split; split; auto; omega.
  split.
  rewrite Z.max_r in * by omega.
  rewrite Zlength_sublist; try omega.
  rewrite Z.max_r in * by omega.
  unfold sublist.
 rewrite Zfirstn_exact_length 
    by (rewrite Zlength_skipn, (Z.max_r 0 (mid-lo)), Z.max_r by omega; omega).
  clear - H1.
  revert v H1; induction (Z.to_nat (mid-lo)); intros. simpl; auto.
  destruct v. constructor. simpl. apply IHn. inv H1; auto.
  split; auto.
  rewrite field_compatible0_cons with (gfs0 := gfs) in H2,H3.
  destruct (nested_field_type2 t gfs) eqn:?; try contradiction.
  destruct H2, H3.
  rewrite !field_compatible0_cons with (gfs0 := gfs), Heqt0. split; auto. omega.
  rewrite Z.max_r by omega.
  intros [? [? [[? ?] [[? ?] [? ?]]]]].
  rewrite Z.max_r  in * by omega.
  assert (Zlength v = hi-lo). {
  clear - H4 H H0.
  unfold sublist in H0, H4.
  rewrite Zlength_firstn in H0,H4.
  simpl skipn in *.
  rewrite Z.max_r in H0 by omega.
  destruct (zlt (Zlength v) (mid-lo)).
  rewrite Z.min_r in H0 by omega. omega.
  clear H0. rewrite Z.max_r in H4 by omega.
  rewrite Zlength_skipn in H4. 
  rewrite (Z.max_r 0 (mid-lo)) in H4 by omega.
  rewrite (Z.max_r) in H4 by omega.
  rewrite Z.min_r in H4 by omega. omega.
}
 split; auto.
  clear H0 H4.  
  split3.
  unfold sublist in H1,H5. simpl skipn in H1.
  rewrite Z.sub_0_r in *.
  rewrite Zfirstn_exact_length in H5
    by (rewrite Zlength_skipn, (Z.max_r 0 (mid-lo)), Z.max_r by omega; omega).
  replace (hi-lo) with (Z.of_nat (Z.to_nat (mid-lo)+ Z.to_nat(hi-mid))) in H8
   by (rewrite <- Z2Nat.inj_add, Z2Nat.id by omega; omega).
  rewrite Zlength_correct in *. apply Nat2Z.inj in H8.
  clear - H8 H5 H1.
  revert v H8 H1 H5; induction (Z.to_nat (mid-lo)); intros. 
  simpl in H5; auto.
  destruct v; simpl in *.
  constructor.
  inv H1.
  constructor; auto.
  auto. auto.
*
  intros [? [? [? ?]]].
  rewrite Z.max_r in H0 by omega.
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
  rewrite split2_array_at with (lo := ml) (mid := mr) (hi := hi) by omega.
  rewrite sepcon_assoc.
  f_equal.
  f_equal.
  rewrite sublist_sublist; try omega. f_equal.  f_equal; omega.
  rewrite Zlength_sublist by omega.
  rewrite sublist_sublist; try omega. f_equal.  f_equal; omega.
Qed.


Lemma split3_array_at: forall sh t gfs lo mid hi v v0 p,
  lo <= mid < hi ->
  Zlength v = hi-lo ->
  JMeq v0 (Znth (mid-lo) v (default_val _)) ->
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
  unfold sublist. replace (mid + 1 - lo - (mid - lo)) with 1 by omega.
  change (Z.to_nat 1) with 1%nat.
  rewrite array_at_len_1 with (v0:=v0).
  rewrite prop_true_andp; auto.
  replace (firstn 1 (skipn (Z.to_nat (mid - lo)) v)) 
     with (Znth (mid-lo) v (default_val (nested_field_type2 t (ArraySubsc 0 :: gfs))) :: nil).
  clear - H0 e.
  pose proof (nested_field_type2_ArraySubsc t mid gfs).
  forget (nested_field_type2 t (ArraySubsc 0 :: gfs)) as t1. 
  forget (nested_field_type2 t (ArraySubsc mid :: gfs)) as t2.
  subst t1; apply JMeq_eq in H0; subst; apply JMeq_refl.
  unfold Znth. rewrite if_false by omega.
  forget (default_val (nested_field_type2 t (ArraySubsc 0 :: gfs))) as w.
  assert (length v > Z.to_nat (mid-lo))%nat.
  apply Nat2Z.inj_gt. rewrite <- Zlength_correct,  Z2Nat.id by omega. omega.
  clear - H1.
  revert v H1; induction (Z.to_nat (mid-lo)); intros.
  destruct v; inv H1.
  reflexivity. reflexivity.
  destruct v. inv H1. simpl skipn.
  rewrite <- IHn. reflexivity. simpl in H1. omega.
  symmetry. rewrite H0. clear H0.
  apply eq_JMeq.
  forget (default_val (nested_field_type2 t (ArraySubsc 0 :: gfs))) as w.
  unfold Znth. rewrite !if_false by omega.
  change (Z.to_nat 0) with O.
  assert (length v > Z.to_nat (mid-lo))%nat. apply Nat2Z.inj_gt. rewrite Z2Nat.id by omega.
  rewrite <- Zlength_correct; omega.
  clear - H0; revert v H0; induction (Z.to_nat (mid-lo)); intros.
  destruct v. inv H0. reflexivity.
  destruct v. reflexivity. simpl skipn. simpl in H0; rewrite <- IHn by omega. reflexivity.
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

Lemma field_at_data_at: forall sh t gfs v (p: val),
  field_at sh t gfs v p =
  data_at sh (nested_field_type2 t gfs) v (field_address t gfs p).
Proof.
  intros.
  unfold data_at, field_at.
  rewrite (nested_field_offset2_ind (nested_field_type2 t gfs) nil) by (simpl; tauto).
  unfold field_address.
  if_tac.
  +
   unfold at_offset; normalize. f_equal.
   apply ND_prop_ext; intuition.
   destruct p; try (destruct H; contradiction).
  generalize (field_compatible_nested_field t gfs (Vptr b i));
  unfold at_offset; solve_mod_modulus; intros. auto.
  +
    apply pred_ext; normalize. destruct H0; contradiction.
Qed.

Lemma field_at__data_at_: forall sh t gfs p,
  field_at_ sh t gfs p =
  data_at_ sh (nested_field_type2 t gfs) (field_address t gfs p).
Proof.
  intros.
  unfold data_at_, field_at_. apply field_at_data_at.
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

Lemma value_fits_JMeq:
  forall sh t t' v v', 
   t=t' -> JMeq v v' -> value_fits sh t v -> value_fits sh t' v'.
Proof.
intros. subst. apply JMeq_eq in H0. subst. 
auto.
Qed.

Lemma array_at_data_at: forall sh t gfs lo hi v p,
  array_at sh t gfs lo hi v p =
  (!! field_compatible0 t (ArraySubsc lo :: gfs) p) &&
  (!! field_compatible0 t (ArraySubsc hi :: gfs) p) &&
  at_offset (data_at sh (nested_field_array_type t gfs lo hi) 
                (@fold_reptype _ (nested_field_array_type t gfs lo hi)  v))
               (nested_field_offset2 t (ArraySubsc lo :: gfs)) p.
Proof.
  intros.
  unfold array_at.
  rewrite at_offset_eq.
  rewrite data_at_data_at'.
  unfold nested_field_array_type.
  rewrite data_at'_ind.
  rewrite <- at_offset_eq.
  rewrite at_offset_array_pred.
  destruct (field_compatible0_dec t (ArraySubsc lo :: gfs) p);
   [ | apply pred_ext; normalize].
  destruct (field_compatible0_dec t (ArraySubsc hi :: gfs) p);
   [ | apply pred_ext; normalize].
  pose proof field_compatible0_nested_field_array t gfs lo hi p f f0.
  normalize.
  f_equal.
*
  fold (nested_field_array_type t gfs lo hi).
  generalize f; intros [_  [_ [_ [_ [_ [_ [_ [_ Ha]]]]]]]].
  destruct (nested_field_type2 t gfs) eqn:?;  try contradiction.
  clear Ha.
  assert (Hv': exists v': list (reptype t0), JMeq v v').
    revert v. rewrite nested_field_type2_ind, Heqt0; eauto.
 destruct Hv' as [v' Hv']. 
  apply ND_prop_ext.
  split.
  intros [? ?].
  split; auto. split; auto.
 cut (value_fits (readable_share_dec sh)
       (Tarray t0 (hi-lo) a)  (@fold_reptype _ (Tarray t0 (hi-lo) a) v')).
 intro.
 eapply value_fits_JMeq; try eassumption.
 unfold nested_field_array_type; 
 do 2 rewrite nested_field_type2_ind; rewrite Heqt0; reflexivity.
 rewrite ! fold_reptype_JMeq. auto.
 rewrite value_fits_ind. 
 rewrite unfold_fold_reptype.
 split.
 clear - Hv' H0 Heqt0.
 generalize dependent v.
 rewrite nested_field_type2_ind. rewrite Heqt0. simpl.
 intros.
 apply JMeq_eq in Hv'. subst v'; auto.
 admit.  (* tedious *)
 intros [_ [? _]].
 assert (value_fits (readable_share_dec sh)
       (Tarray t0 (hi-lo) a)  (@fold_reptype _ (Tarray t0 (hi-lo) a) v')).
 eapply value_fits_JMeq; try eassumption.
 unfold nested_field_array_type. f_equal.
 rewrite nested_field_type2_ind.
 rewrite Heqt0; reflexivity. rewrite Heqt0; reflexivity.
 rewrite ! fold_reptype_JMeq. auto.
 clear H0.
 rewrite value_fits_ind in H1.
 rewrite unfold_fold_reptype in H1.
 admit. (* tedious *)
*
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

Lemma array_at_data_at':   
forall sh t gfs lo hi v p,
  field_compatible0 t (ArraySubsc lo :: gfs) p ->
  field_compatible0 t (ArraySubsc hi :: gfs) p ->
  array_at sh t gfs lo hi v p =
  data_at sh (nested_field_array_type t gfs lo hi) 
                (@fold_reptype _ (nested_field_array_type t gfs lo hi)  v)
               (field_address0 t (ArraySubsc lo::gfs) p).
Proof.
  intros.
  rewrite array_at_data_at.
  rewrite !prop_true_andp by auto.
  unfold at_offset.
  f_equal.
  unfold field_address0.
  rewrite if_true; auto.
Qed.

Lemma array_at_data_at_with_tl: forall sh t gfs lo mid hi v v' p,
  array_at sh t gfs lo mid v p * array_at sh t gfs mid hi v' p =
  data_at sh (nested_field_array_type t gfs lo mid) (@fold_reptype _ (nested_field_array_type t gfs lo mid)  v) (field_address0 t (ArraySubsc lo :: gfs) p) *
  array_at sh t gfs mid hi v' p.
Proof.
  intros.
  rewrite (array_at_data_at sh t gfs lo mid).
  unfold data_at, array_at.
  rewrite at_offset_eq. normalize.
  unfold field_address0.
  destruct (field_compatible0_dec t (ArraySubsc lo :: gfs) p).
  + normalize.
    f_equal.
    apply ND_prop_ext; tauto.
  + rewrite prop_and. rewrite prop_and.
      replace (!! field_compatible0 t (ArraySubsc lo :: gfs) p: mpred) with FF
      by (apply ND_prop_ext; tauto).
    rewrite field_at_isptr with (p := Vundef).
    change (!!isptr Vundef: mpred) with FF.    
    normalize.
   apply pred_ext. normalize. apply FF_left.
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
   rewrite <- !gather_prop_left.
    apply andp_derives; auto.
    apply andp_derives; auto.
    apply prop_derives; auto.
    admit.  (* tedious *)
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
      apply data_at'_data_at'_; try tauto. omega.
    - assert (sizeof cenv_cs (nested_field_type2 t gfs) = 0)
        by (pose proof sizeof_pos cenv_cs (nested_field_type2 t gfs); omega).
      rewrite !empty_data_at' by tauto.
      auto.
  + unfold field_at_, field_at.
    normalize.
Qed.

Lemma field_at_field_at_default : forall sh t gfs v v' p,
  v' = default_val (nested_field_type2 t gfs) ->
  field_at sh t gfs v p |-- field_at sh t gfs v' p.
Proof.
  intros; subst.
  apply field_at_field_at_.
Qed.

Lemma field_at__memory_block: forall sh t gfs p, 
  field_at_ sh t gfs p =
  memory_block sh (sizeof cenv_cs (nested_field_type2 t gfs)) (field_address t gfs p).
Proof.
  intros. 
  unfold field_address.
  destruct (field_compatible_dec t gfs p).
  + unfold field_at_, field_at.
    rewrite prop_true_andp; [ | split; auto].
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
    -
      apply default_value_fits.
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
  v' = default_val (nested_field_type2 t nil) ->
  data_at sh t v p |-- data_at sh t v' p.
Proof.
  intros; subst.
  apply data_at_data_at_.
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
  eapply derives_trans; [apply andp_right; [apply array_at_local_facts | apply derives_refl] | ].
 normalize.
  unfold array_at_.
  apply array_at_ext_derives.
  rewrite H1. rewrite Zlength_correct, length_list_repeat.
 rewrite Z2Nat_id'; auto.
  intros.
  destruct (field_compatible0_dec t (ArraySubsc i :: gfs) p).
  + 
    revert u1 H5; erewrite <- nested_field_type2_ArraySubsc with (i0 := i); intros.
    rewrite H5. unfold Znth. rewrite if_false by omega. 
    rewrite nth_list_repeat.
   apply field_at_field_at_; auto.
  + unfold field_at.
     normalize. 
    contradiction (field_compatible_field_compatible0 t (ArraySubsc i :: gfs) p H6).
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
  replace (Vptr b (Int.repr ofs)) with (offset_val (Int.repr 0) (Vptr b (Int.repr ofs))) at 2.
  + apply memory_block_valid_pointer with (i := 0); auto; omega.
  + simpl.
    rewrite add_repr, Z.add_0_r.
    auto.
Qed.

Lemma data_at_valid_ptr:
  forall sh t v p,
     sepalg.nonidentity sh ->
     sizeof cenv_cs t > 0 ->
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
     sizeof cenv_cs (nested_field_type2 t path) > 0 ->
     field_at sh t path v p |-- valid_pointer (field_address t path p).
Proof.
intros.
rewrite field_at_data_at.
apply data_at_valid_ptr; auto.
Qed.

Lemma field_at_valid_ptr0:
  forall sh t path v p, 
     sepalg.nonidentity sh ->
     sizeof cenv_cs (nested_field_type2 t path) > 0 ->
     nested_field_offset2 t path = 0 ->
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

Hint Resolve data_at_valid_ptr field_at_valid_ptr field_at_valid_ptr0 : valid_pointer.

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


Lemma compute_legal_nested_field_spec':
  forall t gfs,
  Forall Datatypes.id (compute_legal_nested_field t gfs) ->
  legal_nested_field t gfs.
Proof.
  intros.
  induction gfs as [| gf gfs].
  + simpl; auto.
  +  simpl in H|-*.
    unfold legal_field. unfold nested_field_type2 in *.
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
    match (nested_field_type2 t gfs0), gf with
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
     unfold nested_field_type2 in *.
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
  0 < sizeof cenv_cs (nested_field_type2 t fld) < Int.modulus ->
  legal_alignas_type t = true ->
  field_at sh t fld v p * field_at sh t fld v' p|-- FF.
Proof.
  intros.
  eapply derives_trans.
  + apply sepcon_derives. 
    apply field_at_field_at_; try assumption; auto. 
    apply field_at_field_at_; try assumption; auto. 
  + fold (field_at_ sh t fld p).
    rewrite field_at__memory_block by auto.
    normalize.
    apply memory_block_conflict; try  (unfold Int.max_unsigned; omega).
    apply sepalg.nonidentity_nonunit; auto.
Qed.

Lemma data_at_conflict: forall sh t v v' p,
  sepalg.nonidentity sh ->
  field_compatible t nil p ->
  0 < sizeof cenv_cs t < Int.modulus ->
  data_at sh t v p * data_at sh t v' p |-- FF.
Proof.
  intros. unfold data_at. apply field_at_conflict; auto.
  destruct H0 as [? [? ?]]; auto. 
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  sepalg.nonidentity sh ->
  0 < sizeof cenv_cs (nested_field_type2 t fld) < Int.modulus ->
  legal_alignas_type t = true ->
        field_at_ sh t fld p
        * field_at_ sh t fld p |-- FF.
Proof.
intros.
apply field_at_conflict; auto.
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
  readable_share sh ->
  var_block sh (id, t) = `(data_at_ sh t) (eval_lvar id t).
Proof.
  intros; extensionality rho.
 unfold var_block.
  unfold_lift.
  simpl.
  apply Zlt_is_lt_bool in H2.
  rewrite data_at__memory_block; try auto.
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

Lemma data_array_at_local_facts {cs: compspecs}:
 forall t' n a sh v p,
  data_at sh (Tarray t' n a) v p |-- 
  !! (field_compatible (Tarray t' n a) nil p 
     /\ Zlength (unfold_reptype v) = Z.max 0 n
     /\ Forall (value_fits (readable_share_dec sh) t') (unfold_reptype v)).
Proof.
intros.
eapply derives_trans; [apply data_at_local_facts |].
apply prop_derives.
intros [? ?]; split; auto.
Qed.


Lemma value_fits_false_by_value {cs: compspecs}:
  forall t v, 
   type_is_by_value t = true ->
   value_fits false t v = True.
Proof.
intros.
rewrite value_fits_ind; destruct t; inv H; 
simpl; if_tac; auto.
Qed.

Lemma value_fits_true_by_value {cs: compspecs}:
  forall t v, 
   type_is_volatile t = false ->
   type_is_by_value t = true ->
   value_fits true t v = tc_val' t (repinject t v).
Proof.
intros.
rewrite value_fits_ind; destruct t; inv H; inv H0;
simpl; rewrite H2; auto.
Qed.

Ltac field_at_saturate_local :=
unfold data_at;
match goal with |- field_at ?sh ?t ?path ?v ?c |-- _ =>
eapply derives_trans; [apply field_at_local_facts |];
  cbv beta;
  try rewrite proj_sumbool_is_true by auto;
  try rewrite proj_sumbool_is_false by auto;
  let p := fresh "p" in set (p := nested_field_type2 t path);
  simpl in p; unfold field_type in p; simpl in p; subst p;
  try rewrite value_fits_false_by_value by reflexivity;
  try rewrite value_fits_true_by_value by reflexivity;
  try match goal with |- context [repinject ?t ?v] =>
    change (repinject t v) with v
  end;
  apply derives_refl
end.


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
  (apply data_array_at_local_facts) : saturate_local.
Hint Extern 0 (data_at _ (tarray _ _) _ _ |-- _) => 
  (apply data_array_at_local_facts) : saturate_local.
Hint Rewrite <- @field_at_offset_zero: norm1.
Hint Rewrite <- @field_at__offset_zero: norm1.
Hint Rewrite <- @field_at_offset_zero: cancel.
Hint Rewrite <- @field_at__offset_zero: cancel.
Hint Rewrite <- @data_at__offset_zero: norm1.
Hint Rewrite <- @data_at_offset_zero: norm1.
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

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at _ _ _ _ _) =>
  (apply field_at_field_at_default; reflexivity) : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- data_at_ _ _ _) =>
    (apply data_at_data_at_) : cancel.

Hint Extern 1 (data_at _ _ _ _ |-- memory_block _ _ _) =>
    (simple apply data_at__memory_block_cancel) : cancel.

Hint Extern 2 (data_at _ _ _ _ |-- data_at _ _ _ _) =>
  (apply data_at_data_at_default; reflexivity) : cancel.

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
 | |- context [@field_at ?cs ?sh ?t ?gfs ?v ?p] =>
     let id := fresh "id" in evar (id: ident);
     let Heq := fresh "Heq" in
     assert (Heq: nested_field_type2 t gfs = Tstruct id noattr)
           by (unfold id; reflexivity);
     let H := fresh in 
     assert (H:= @field_at_Tstruct cs sh t gfs id noattr
                          v v p  Heq (JMeq_refl _));
     unfold id in H; clear Heq id;
     let FLD := fresh "FLD" in
     forget (@field_at cs sh t gfs v p) as FLD;
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

Lemma field_at_ptr_neq{cs: compspecs} :
   forall sh t fld p1 p2 v1 v2,
  sepalg.nonidentity sh ->
 0 < sizeof cenv_cs (nested_field_type2 t (fld :: nil)) < Int.modulus ->
 legal_alignas_type t = true ->
   field_at sh t (fld::nil) v1 p1 *
   field_at sh t (fld::nil) v2 p2
   |--
   !! (~ ptr_eq p1 p2).
Proof.
   intros.
   apply not_prop_right; intros.
   apply ptr_eq_e in H2; rewrite -> H2.
   apply field_at_conflict; try assumption.
Qed.

Lemma field_at_ptr_neq_andp_emp{cs: compspecs} : 
    forall sh t fld p1 p2 v1 v2,
  sepalg.nonidentity sh ->
 0 < sizeof cenv_cs (nested_field_type2 t (fld :: nil)) < Int.modulus ->
 legal_alignas_type t = true ->
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

Lemma data_at'_void:
  forall {cs: compspecs} 
      sh t v q, t = Tvoid -> data_at' sh t v q = FF.
Proof.
 intros; subst. unfold data_at'; simpl. unfold mapsto.
  if_tac; reflexivity.
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
unfold field_type. unfold fieldlist.field_type2. simpl.
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

Definition snd_reptype_structlist  {cs: compspecs}
         (p q: ident*type) (m: list (ident*type))
         (H: members_no_replicate (p::q::m) = true) 
         (v: reptype_structlist (p::q::m)) : reptype_structlist (q::m).
  (* not useful? *)
destruct v.
unfold reptype_structlist.
cut (map
         (fun it : ident * type =>
          reptype (field_type (fst it) (p :: q :: m))) (q :: m) =
   map (fun it : ident * type => reptype (field_type (fst it) (q :: m)))
     (q :: m)).
intro.
forget (map
       (fun it : ident * type => reptype (field_type (fst it) (p :: q :: m)))
       (q :: m)) as T.
subst T. apply c.
apply snd_reptype_structlist_aux; auto.
Defined.

Lemma snd_reptype_structlist_eq  {cs: compspecs}:
  forall p q m H v,
      @JMeq _ (snd_reptype_structlist p q m H v) _ (snd v).
  (* not useful? *)
intros.
Admitted. (* for Qinxiang? *)

Lemma field_at_share_join_aux {cs: compspecs}:
  forall sh1 sh2 sh m,
   members_no_replicate m = true ->
   sepalg.join sh1 sh2 sh ->
  (Forall  (fun it : ident * type =>
        forall (v : reptype (field_type (fst it) m))
          (q : val),
        data_at' sh1 (field_type (fst it) m) v q *
        data_at' sh2 (field_type (fst it) m) v q =
        data_at' sh (field_type (fst it) m) v q)
       m) ->
  forall (sz: Z) (v: reptype_structlist m) (q: val),
struct_pred m
  (fun (it : ident * type)
     (v0 : reptype (field_type (fst it) m)) =>
   withspacer sh1
     (field_offset cenv_cs (fst it) m +
      sizeof cenv_cs (field_type (fst it) m))
     (field_offset_next cenv_cs (fst it) m
        sz)
     (at_offset
        (data_at' sh1 (field_type (fst it) m) v0)
        (field_offset cenv_cs (fst it) m))) v q *
struct_pred m
  (fun (it : ident * type)
     (v0 : reptype (field_type (fst it) m)) =>
   withspacer sh2
     (field_offset cenv_cs (fst it) m +
      sizeof cenv_cs (field_type (fst it) m))
     (field_offset_next cenv_cs (fst it) m
        sz)
     (at_offset
        (data_at' sh2 (field_type (fst it) m) v0)
        (field_offset cenv_cs (fst it) m))) v q =
struct_pred m
  (fun (it : ident * type)
     (v0 : reptype (field_type (fst it) m)) =>
   withspacer sh
     (field_offset cenv_cs (fst it) m +
      sizeof cenv_cs (field_type (fst it) m))
     (field_offset_next cenv_cs (fst it) m
        sz)
     (at_offset
        (data_at' sh (field_type (fst it) m) v0)
        (field_offset cenv_cs (fst it) m))) v q.
Proof.
intros until m; intros HM H H0 sz.
induction m; intros.
* (* nil case *) 
  simpl. normalize.
* (*cons case *)
  destruct a as [i t].
  destruct m.
 + unfold struct_pred. simpl.
    rewrite !withspacer_spacer.
    rewrite <- !sepcon_assoc.
    forget (field_offset cenv_cs i ((i, t) :: nil) +
    sizeof cenv_cs (field_type i ((i, t) :: nil))) as J.
    forget (field_offset_next cenv_cs i ((i, t) :: nil) sz) as K.
    pull_left (spacer sh2 J K q);
    pull_left (spacer sh1 J K q).
    rewrite sepcon_assoc.
    f_equal.
    apply spacer_share_join; auto.
    unfold at_offset.
    inv H0.
    apply H3.
 +
    pose (Q sh mems := 
 (fun (it : ident * type)
     (v0 : reptype (field_type (fst it) mems)) =>
   withspacer sh
     (field_offset cenv_cs (fst it) mems +
      sizeof cenv_cs (field_type (fst it) mems))
     (field_offset_next cenv_cs (fst it) mems sz)
     (at_offset (data_at' sh (field_type (fst it) mems) v0)
        (field_offset cenv_cs (fst it) mems)))).
   fold (Q sh1 ((i, t) :: p :: m)).
   fold (Q sh2 ((i, t) :: p :: m)).
   fold (Q sh ((i, t) :: p :: m)).
   fold (Q sh1 (p::m)) in IHm.
   fold (Q sh2 (p::m)) in IHm.
   fold (Q sh (p::m)) in IHm.
   generalize HM; intro HM'.
    assert (Hv' := snd_reptype_structlist_eq (i,t) p m HM' v).
    rewrite fieldlist.members_no_replicate_ind in HM.
    destruct HM as [HM1 HM].
    rewrite !struct_pred_cons2.
    unfold Q at 1 3 5. rewrite !withspacer_spacer.
    rewrite <- !sepcon_assoc.
    forget (field_offset cenv_cs (fst (i, t)) ((i, t) :: p :: m) +
   sizeof cenv_cs (field_type (fst (i, t)) ((i, t) :: p :: m))) as J.
    forget(field_offset_next cenv_cs (fst (i, t)) ((i, t) :: p :: m) sz) as K.
    pull_left (spacer sh2 J K q);
    pull_left (spacer sh1 J K q).
    do 3 rewrite sepcon_assoc; rewrite (sepcon_assoc (spacer sh J K q)).
    f_equal.
    apply spacer_share_join; auto.
    unfold at_offset.
    specialize (IHm HM).
    inv H0. simpl in H3.
  forget (offset_val
     (Int.repr (field_offset cenv_cs (fst (i, t)) ((i, t) :: p :: m))) q) as q'.
  simpl @fst.
  repeat rewrite <- sepcon_assoc.
  match goal with |- ?A * ?B * ?C * ?D = _ => pull_left C end.
  rewrite sepcon_assoc.
  f_equal.
  rewrite sepcon_comm.
  apply H3.
   clear H3.
   spec IHm.
   clear - H4 HM1.
   eapply Forall_impl; try apply H4; clear H4; intros.
   destruct (ident_eq (fst a) i).
    subst i.
   pose proof (fieldlist.not_in_members_field_type2 _ _ HM1).
   repeat rewrite data_at'_void by auto. normalize.
   simpl in H.
   assert (field_type (fst a) (p::m) = field_type (fst a) ((i,t)::p::m) ). {
     unfold field_type. unfold fieldlist.field_type2.
     simpl. rewrite if_false by auto. auto.
   }
   forget (field_type (fst a) (p :: m)) as T.
   forget (field_type (fst a) ((i, t) :: p :: m)) as U. subst U.
   auto.
   clear H4.
   specialize (IHm (snd_reptype_structlist (i, t) p m HM' v) q).
   cut (forall sh, struct_pred (p::m) (Q sh ((i,t)::p::m)) (snd v) q =
                         struct_pred (p::m) (Q sh (p::m)) (snd_reptype_structlist (i, t) p m HM' v) q).
   intro. 
   rewrite !H0. auto.
   clear - Hv'. subst Q. intros.
   admit. (* for Qinxiang? *)
Qed.


Lemma data_at'_share_join {cs: compspecs}:
  forall sh1 sh2 sh t v p,
    sepalg.join sh1 sh2 sh ->
   data_at' sh1 t v p * data_at' sh2 t v p = data_at' sh t v p.
Proof.
intros; rename p into q; 
 revert v q; pattern t;  type_induction.type_induction t; intros;
rewrite !data_at'_ind;
 try solve [if_tac;
     [ apply memory_block_share_join; auto
     | apply mapsto_share_join; auto]];
  try solve [normalize].
* (* Tarray *)
  destruct (zlt z 0). rewrite !array_pred_len_0 by omega. normalize.
  forget (unfold_reptype v) as vl.  simpl in vl. clear v. unfold reptype_array in vl.
  rewrite <- (Z2Nat.id z) by omega.
  remember (Z.to_nat z) as n. clear z Heqn g.
  unfold array_pred, aggregate_pred.array_pred.
  rewrite !Z.sub_0_r.
replace (fun i : Z =>
   at_offset (data_at' sh1 t0 (Znth (i - 0) vl (default_val t0)))
     (sizeof cenv_cs t0 * i))
 with (fun i : Z =>
   at_offset (data_at' sh1 t0 (Znth i vl (default_val t0)))
     (sizeof cenv_cs t0 * i))
  by (extensionality i; rewrite Z.sub_0_r; auto).
replace (fun i : Z =>
   at_offset (data_at' sh2 t0 (Znth (i - 0) vl (default_val t0)))
     (sizeof cenv_cs t0 * i))
 with (fun i : Z =>
   at_offset (data_at' sh2 t0 (Znth i vl (default_val t0)))
     (sizeof cenv_cs t0 * i))
  by (extensionality i; rewrite Z.sub_0_r; auto).
replace (fun i : Z =>
   at_offset (data_at' sh t0 (Znth (i - 0) vl (default_val t0)))
     (sizeof cenv_cs t0 * i))
 with (fun i : Z =>
   at_offset (data_at' sh t0 (Znth i vl (default_val t0)))
     (sizeof cenv_cs t0 * i))
  by (extensionality i; rewrite Z.sub_0_r; auto).
  forget 0 as lo.
  revert lo vl ; induction n; intros.
  simpl. apply sepcon_emp.
  rewrite Nat2Z.id. simpl.
  repeat rewrite <- sepcon_assoc.
  match goal with |- ?A * ?B * ?C * ?D = _ => pull_left C end.
  rewrite sepcon_assoc.
  f_equal. 
  rewrite sepcon_comm. unfold at_offset. apply IH.
  specialize (IHn (Z.succ lo)).
  rewrite Nat2Z.id in IHn.
  apply IHn. 
* (* Tstruct *)
  clear - H IH.
 apply field_at_share_join_aux; auto.
 apply (get_co_members_no_replicate id).
* (* Tunion *)
  admit. (* similar to the Tstruct case? *)
Qed.

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
Admitted. (* should be easy *)

Lemma value_fits_relax {cs: compspecs}:
  forall  sh t v, value_fits true t v -> value_fits sh t v.
Proof.
intros sh t.
destruct sh; auto.
type_induction t; intros v;
rewrite !value_fits_ind; simpl; intros; auto;
try solve [if_tac; auto].
* (* array case *)
destruct H; split; auto.
clear H.
induction (unfold_reptype v). constructor.
inv H0.
constructor; auto.
* (* struct case *)
admit.
* (* union case *)
admit.
Qed.

Lemma field_at_share_join{cs: compspecs}:
  forall sh1 sh2 sh t gfs v p,
    sepalg.join sh1 sh2 sh ->
   field_at sh1 t gfs v p * field_at sh2 t gfs v p = field_at sh t gfs v p.
Proof.
intros.
unfold field_at.
normalize.
f_equal.
apply ND_prop_ext.
split. intros [? [? [? ?]]]; split; auto.
destruct (readable_share_dec sh1); simpl in H1.
apply value_fits_relax; auto.
destruct (readable_share_dec sh2).
apply value_fits_relax; auto.
pose proof (@join_unreadable_shares _ _ _ H n n0).
destruct (readable_share_dec sh); try contradiction; auto.
intros [? ?]; split3; auto; [ | split; auto].
destruct (readable_share_dec sh).
apply value_fits_relax; auto.
destruct (readable_share_dec sh1); auto.
pose proof (readable_share_join _ _ _ H r); contradiction.
destruct (readable_share_dec sh).
apply value_fits_relax; auto.
destruct (readable_share_dec sh2); auto.
pose proof (readable_share_join _ _ _ (sepalg.join_comm H) r); contradiction.
unfold at_offset.
apply data_at'_share_join; auto.
Qed.

Lemma field_at__share_join{cs: compspecs}:
  forall sh1 sh2 sh t gfs p,
    sepalg.join sh1 sh2 sh ->
   field_at_ sh1 t gfs p * field_at_ sh2 t gfs p = field_at_ sh t gfs p.
Proof.
intros.
unfold field_at_.
apply field_at_share_join.
auto.
Qed.

Lemma nonreadable_memory_block_data_at':
   forall {cs: compspecs} sh t v p,
   ~ readable_share sh ->
    field_compatible t nil p ->
    memory_block sh (sizeof cenv_cs t) p = data_at' sh t v p.
Proof.
intros.
hnf in H0.
destruct H0 as [Hp [? [_ [Hcom [Hsz [Hsc [Hal Hlnf]]]]]]].
revert H0 Hsz v p Hcom Hsc Hp Hal Hlnf; pattern t; type_induction.type_induction t; intros; inv H0;
 rewrite  data_at'_ind; auto;
match goal with
| |- appcontext [type_is_volatile ?t] =>
       destruct (type_is_volatile t) eqn:HH; [auto | rewrite memory_block_mapsto_ by auto];
       unfold mapsto_, mapsto; destruct (access_mode t); auto;
       rewrite HH; simpl;
       destruct p; auto;
       rewrite !if_false by auto; auto
| _ => idtac
end.

* inversion Hcom.
* (* Tarray *)
  admit.  (* Qinxiang *)
* inversion Hcom.
* (* Tstruct *)
  admit.  (* Qinxiang *)
* (* Tunion *)
  admit.  (* Qinxiang *)
Qed.

Lemma nonreadable_memory_block_data_at:
  forall  {cs: compspecs}
      sh t v p, 
  ~ readable_share sh ->
   field_compatible t nil p ->
   value_fits false t v ->
   memory_block sh (sizeof cenv_cs t) p = data_at sh t v p.
Proof.
intros.
unfold data_at, field_at.
destruct (readable_share_dec sh); try contradiction.
rewrite prop_true_andp by auto.
change (nested_field_offset2 t nil) with 0.
unfold at_offset.
normalize.
apply nonreadable_memory_block_data_at'; auto.
Qed.

Lemma nonreadable_field_at_eq {cs: compspecs} :
  forall sh t gfs v v' p,
   ~ readable_share sh ->
   (value_fits false (nested_field_type2 t gfs) v <-> value_fits false (nested_field_type2 t gfs) v') ->
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
   memory_block ash (sizeof cenv_cs t) p * data_at bsh t v p = data_at psh t v p.
Proof.
intros.
apply pred_ext; saturate_local.
rewrite nonreadable_memory_block_data_at with (v0:=v); auto.
unfold data_at.
erewrite field_at_share_join; eauto.
destruct (readable_share_dec bsh); auto.
eapply value_fits_relax; eauto.
rewrite nonreadable_memory_block_data_at with (v0:=v); auto.
unfold data_at.
erewrite field_at_share_join; eauto.
destruct (readable_share_dec psh); auto.
eapply value_fits_relax; eauto.
Qed.


Lemma nonreadable_data_at'_eq {cs: compspecs} : 
  forall sh t v v' p,
    ~readable_share sh ->
    field_compatible t nil p ->
     data_at' sh t v p = data_at' sh t v' p.
Proof.
intros.
 rewrite <- !(nonreadable_memory_block_data_at'); auto.
Qed.

Lemma nonreadable_data_at_eq {cs: compspecs}: 
  forall sh t v v' p, ~readable_share sh ->
   (value_fits false t v <-> value_fits false t v') ->
     data_at sh t v p = data_at sh t v' p.
Proof.
intros.
unfold data_at.
apply nonreadable_field_at_eq; auto.
Qed.

Lemma value_fits_Tint_trivial {cs: compspecs} :
  forall sh s a  i, value_fits sh (Tint I32 s a) (Vint i).
Proof.
intros.
rewrite value_fits_ind; simpl.
if_tac; auto.
if_tac; auto.
hnf. intro. apply Coq.Init.Logic.I.
Qed.

Lemma mapsto_data_at {cs: compspecs} sh t v v' p :  (* not needed here *)
  type_is_by_value t = true ->
  type_is_volatile t = false ->
  readable_share sh ->
  isptr p ->
  size_compatible t p ->
  align_compatible t p ->
  legal_alignas_type t = true ->
  legal_cosu_type t = true ->
  complete_type cenv_cs t = true ->
  sizeof cenv_cs t < Int.modulus ->
  (v <> Vundef -> tc_val t v) ->
  JMeq v v' ->
  mapsto sh t p v = data_at sh t v' p.
Proof.
  intros.
  unfold data_at, field_at, at_offset, offset_val.
  simpl.
  destruct p; inv H2.
  rewrite int_add_repr_0_r.
  rewrite by_value_data_at' by auto.
  rewrite <- (repinject_JMeq _ v' H) in H10.
  apply JMeq_eq in H10.
  rewrite prop_true_andp; auto.
  f_equal. auto.
  split.
  repeat split; auto.
  erewrite value_fits_by_value; auto.
  unfold nested_field_type2; simpl.
  rewrite H0. if_tac; auto.
  unfold tc_val'. rewrite <- H10. auto.
Qed.
