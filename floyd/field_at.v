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
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(************************************************

Definition of nested_reptype_structlist, field_at, array_at, nested_sfieldlist_at

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

Definition data_at_ (sh: Share.t) (t: type) := field_at_ sh t.

Definition nested_reptype_structlist t gfs (m: members) := 
  compact_prod (map (fun it => reptype (nested_field_type2 t (StructField (fst it) :: gfs))) m).

Definition nested_reptype_unionlist t gfs (m: members) := 
  compact_sum (map (fun it => reptype (nested_field_type2 t (UnionField (fst it) :: gfs))) m).

(*
Lemma nested_reptype_lemma: forall t gfs t0, nested_field_type t gfs = Some t0 -> reptype t0 = reptype (nested_field_type2 t gfs).
Proof.
  unfold nested_field_type, nested_field_type2.
  intros.
  destruct (nested_field_rec t gfs) as [(ofs', t')|] eqn:HH.
  + inversion H.
    reflexivity.
  + inversion H.
Defined.
*)

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
  (!! field_compatible0 t (ArraySubsc lo :: gfs) p) &&
  (!! field_compatible0 t (ArraySubsc hi :: gfs) p) &&
  array_pred lo hi (default_val _)
    (fun i v => at_offset (data_at' sh (nested_field_type2 t (ArraySubsc 0 :: gfs)) v)
       (nested_field_offset2 t (ArraySubsc i :: gfs))) v p.

Definition array_at_ (sh: Share.t) (t: type) (gfs: list gfield) (lo hi: Z) :=
  array_at sh t gfs lo hi nil.

Lemma field_at_local_facts: forall sh t gfs v p,
  field_at sh t gfs v p |-- !! isptr p.
Proof.
  intros.
  unfold field_at.
  apply andp_left1.
  apply prop_derives.
  apply field_compatible_isptr.
Qed.

Opaque alignof.

(*
Lemma nested_Znth_app_l: forall {t gfs} lo i (ct1 ct2: list (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs)))),
  0 <= i - lo < Zlength ct1 ->
  nested_Znth lo i ct1 = nested_Znth lo i (ct1 ++ ct2).
Proof.
  intros.
  unfold nested_Znth.
  f_equal.
  unfold Znth.
  if_tac; [omega |].
  rewrite app_nth1; [reflexivity |].
  destruct H as [_ ?].
  apply Z2Nat.inj_lt in H; [| omega | omega].
  rewrite Zlength_correct in H.
  rewrite Nat2Z.id in H.
  exact H.
Qed.

Lemma nested_Znth_app_r: forall {t gfs} lo i (ct1 ct2: list (reptype (nested_field_type2 t (ArraySubsc 0 :: gfs)))),
  i - lo >= Zlength ct1 ->
  nested_Znth (lo + Zlength ct1) i ct2 = nested_Znth lo i (ct1 ++ ct2).
Proof.
  intros.
  unfold nested_Znth.
  f_equal.
  unfold Znth.
  assert (Zlength ct1 >= 0).
  Focus 1. {
    rewrite Zlength_correct.
    pose proof Zle_0_nat (length ct1).
    omega.
  } Unfocus.
  if_tac; [omega |].
  if_tac; [omega |].
  rewrite app_nth2.
  + f_equal.
    replace (i - (lo + Zlength ct1)) with (i - lo - Zlength ct1) by omega.
    rewrite Z2Nat.inj_sub by omega.
    rewrite Zlength_correct.
    rewrite Nat2Z.id.
    reflexivity.
  + rewrite <- (Nat2Z.id (length ct1)).
    rewrite <- Zlength_correct.
    apply Z2Nat.inj_le; omega.
Qed.
*)

Lemma prop_ext: forall P Q, (P <-> Q) -> (@eq mpred) (!! P) (!! Q).
Proof.
  intros.
  apply pred_ext; apply prop_derives; tauto.
Qed.

(************************************************

Unfold lemmas

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
  + assert (0 <= 0 <= n /\ 0 <= n <= n) by omega; normalize; apply prop_ext; tauto.
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
  | (!! field_compatible _ _ _) => apply (derives_trans _ _ _ (prop_derives _ _ (field_compatible_isptr _ _ _))); solve_ptr_derives
  | (!! field_compatible0 _ _ p) => apply (derives_trans _ _ _ (prop_derives _ _ (field_compatible0_isptr _ _ _))); solve_ptr_derives
  | (withspacer _ _ _ ?P p) => apply withspacer_preserve_local_facts;
                                     intro p0; solve_ptr p0 (P p0)
  | (at_offset ?P _ p) => apply at_offset_preserve_local_facts;
                                     intro p0; solve_ptr p0 (P p0)
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
Goal forall sh t gfs p, !! field_compatible t gfs (offset_val Int.zero p) && at_offset (field_at sh t gfs (default_val _)) 14 Vundef = (!! field_compatible0 t gfs p).
intros.
destruct_ptr p.
*)
Hint Rewrite at_offset_eq3 : at_offset_db.
Hint Rewrite withspacer_spacer : at_offset_db.
Hint Rewrite spacer_memory_block using (simpl; auto): at_offset_db.

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
  generalize (co_members (get_co id)) at 1 6; intro m; destruct m; [auto |].
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
      by (apply prop_ext; unfold field_compatible; tauto; apply prop_ext; tauto).
    simpl in n.
    rewrite H in n.
    simpl in n.
    replace (!!field_compatible t gfs (Vptr b (Int.repr ofs)) : mpred) with (FF: mpred)
      by (apply prop_ext; unfold field_compatible; tauto; apply prop_ext; tauto).
    normalize.
  } Unfocus.
  rewrite nested_field_offset2_ind with (gfs0 := StructField i :: gfs) by auto.
  unfold gfield_offset; rewrite H.
  f_equal; [| f_equal].
  + apply prop_ext.
    rewrite field_compatible_cons, H.
    tauto.
  + rewrite sizeof_Tstruct.
    f_equal; [| f_equal]; f_equal; omega.
  + rewrite Z.add_assoc.
    erewrite data_at'_type_changable; [reflexivity | |].
    - simpl.
      rewrite nested_field_type2_ind.
      simpl; rewrite H.
      auto.
    - admit.
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
  generalize (co_members (get_co id)) at 2 3 5; intro m; destruct m; [auto |].
  intro HH; assert (co_members (get_co id) <> nil) by congruence; clear HH.
  apply union_pred_ext; [apply get_co_members_no_replicate | admit |].
  
  intros.
  destruct_ptr p.
  assert (in_members i (co_members (get_co id)))
    by (rewrite H2; apply members_union_inj_in_members; auto).
  unfold field_at, fst, snd.
  autorewrite with at_offset_db.
  unfold offset_val.
  solve_mod_modulus.
  normalize.
  destruct (legal_nested_field_dec t (UnionField i :: gfs)).
  Focus 2. {
    replace (!!field_compatible t (UnionField i :: gfs) (Vptr b (Int.repr ofs)) : mpred) with (FF: mpred)
      by (apply prop_ext; unfold field_compatible; tauto).
    simpl in n.
    rewrite H in n.
    simpl in n.
    replace (!!field_compatible t gfs (Vptr b (Int.repr ofs)) : mpred) with (FF: mpred)
      by (apply prop_ext; unfold field_compatible; tauto).
    normalize.
  } Unfocus.
  rewrite nested_field_offset2_ind with (gfs0 := UnionField i :: gfs) by auto.
  unfold gfield_offset; rewrite H.
  f_equal; [| f_equal].
  + apply prop_ext.
    rewrite field_compatible_cons, H.
    tauto.
  + rewrite sizeof_Tunion.
    f_equal; [| f_equal]; f_equal; omega.
  + rewrite Z.add_0_r.
    erewrite data_at'_type_changable; [reflexivity | |].
    - simpl.
      rewrite nested_field_type2_ind.
      simpl; rewrite H.
      auto.
    - admit.
Qed.
  
(*
Lemma data_at_field_at: forall sh t, data_at sh t = field_at sh t nil.
Proof.
  intros.
  unfold data_at, field_at.
  extensionality v p; simpl.
  pose proof legal_nested_field_nil_lemma t.
  apply pred_ext; normalize.
Qed.

Lemma data_at__field_at_: forall sh t, data_at_ sh t = field_at_ sh t nil.
Proof.
  intros.
  unfold data_at_, field_at_.
  rewrite data_at_field_at.
  reflexivity.
Qed.

Lemma data_at_field_at_cancel:
  forall sh t v p, data_at sh t v p |-- field_at sh t nil v p.
Proof. intros; rewrite data_at_field_at; auto. Qed.

Lemma field_at_data_at_cancel:
  forall sh t v p, field_at sh t nil v p |-- data_at sh t v p.
Proof. intros; rewrite data_at_field_at; auto. Qed.
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
    unfold offset_val.
    solve_mod_modulus.
    rewrite (nested_field_offset2_ind (nested_field_type2 t gfs) nil) by (simpl; tauto).
    rewrite Z.add_0_r.
    f_equal. (* It magically solved the potential second subgoal *)
    apply prop_ext.


simpl.
Check spacer_memory_block.
unfold field_compatible in H.
    destruct H as [? [? [? [? [? ?]]]]].
    unfold data_at.
    simpl.
    rewrite <- at_offset'_eq by (rewrite <- data_at'_offset_zero; reflexivity).
    rewrite <- data_at'_at_offset'; [ |
      apply (nested_field_type2_nest_pred eq_refl), H0 |
      apply nested_field_offset2_type2_divide, H0].
    apply pred_ext; normalize.
    apply andp_right; [| apply derives_refl].
    apply prop_right.
    repeat (try assumption; split).
    - apply (nested_field_type2_nest_pred eq_refl), H1.
    - apply size_compatible_nested_field; assumption.
    - apply align_compatible_nested_field; assumption.
    - apply (nested_field_type2_nest_pred eq_refl), H0.
  + simpl.
    rewrite data_at'_isptr.
    normalize.
    unfold field_compatible in H.
    match goal with
    | |- ?A && _ = _ => replace A with (@FF mpred Nveric) by (apply pred_ext; normalize; tauto)
    end.
    rewrite data_at_isptr.
    simpl.
    change (!!False) with FF.
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

Lemma field_at_compatible:
  forall sh t path v c,
     field_at sh t path v c |-- !! field_compatible t path c.
Proof.
  intros.
  rewrite field_at_data_at.
  rewrite data_at_isptr.
  unfold field_address.
  if_tac.
  + normalize.
  + normalize.
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

Hint Resolve field_at_compatible : saturate_local.

Lemma data_at_compatible: forall sh t v p, data_at sh t v p |-- !! field_compatible t nil p.
Proof. intros.
 rewrite data_at_field_at; apply field_at_compatible.
Qed.
Hint Resolve data_at_compatible : saturate_local.

Lemma data_at__compatible: forall sh t p, data_at_ sh t p |-- !! field_compatible t nil p.
Proof. intros.
 unfold data_at_. apply data_at_compatible.
Qed.
Hint Resolve data_at__compatible : saturate_local.

Lemma field_at_isptr: forall sh t gfs v p,
  field_at sh t gfs v p = (!! isptr p) && field_at sh t gfs v p.
Proof. intros. apply local_facts_isptr. 
 eapply derives_trans; [ apply field_at_compatible | ].
 apply prop_derives; intros [? ?]; auto.
Qed.

Lemma field_at_offset_zero: forall sh t gfs v p,
  field_at sh t gfs v p = field_at sh t gfs v (offset_val Int.zero p).
Proof. intros. apply local_facts_offset_zero.
 intros. rewrite field_at_isptr; normalize.
Qed.

Lemma field_at__compatible: forall sh t gfs p,
  field_at_ sh t gfs p |-- !! field_compatible t gfs p.
Proof.
  intros.
  unfold field_at_.
  apply field_at_compatible.
Qed.
Hint Resolve field_at__compatible : saturate_local.

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

Lemma field_at_field_at_: forall sh t gfs v p, 
  field_at sh t gfs v p |-- field_at_ sh t gfs p.
Proof.
  intros.
  destruct p; try (rewrite field_at_isptr, field_at__isptr; normalize; reflexivity).
  unfold field_at_, field_at.
  simpl; fold size_compatible.
  normalize.
  apply data_at'_data_at'_.
  + apply nested_field_type2_nest_pred; [reflexivity|exact H2].
  + pose proof nested_field_offset2_in_range t gfs H1.
    omega.
  + apply nested_field_offset2_type2_divide, H2.
  + eapply Zdivides_trans; [|exact H0].
    apply alignof_nested_field_type2_divide; auto.
Qed.

Hint Rewrite <- field_at_offset_zero: norm.
Hint Rewrite <- field_at__offset_zero: norm.
Hint Rewrite <- field_at_offset_zero: cancel.
Hint Rewrite <- field_at__offset_zero: cancel.

(* We do these as Hint Extern, instead of Hint Resolve,
  to limit their application and make them fail faster *)

Hint Extern 1 (data_at _ _ _ _ |-- field_at _ _ nil _ _) =>
    (apply data_at_field_at_cancel) : cancel.

Hint Extern 1 (field_at _ _ nil _ _ |-- data_at _ _ _ _) =>
    (apply field_at_data_at_cancel) : cancel.

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at_ _ _ _ _) => 
   (apply field_at_field_at_) : cancel.

Hint Extern 2 (field_at _ _ _ _ _ |-- field_at ?sh ?t ?gfs ?v _) => 
   (change (field_at sh t gfs v) with (field_at_ sh t gfs);
    apply field_at_field_at_) : cancel.

Hint Extern 2 (field_at ?sh ?t ?gfs ?v _ |-- field_at_ _ _ _ _) => 
   (change (field_at sh t gfs v) with (field_at_ sh t gfs);
    apply derives_refl) : cancel.

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

(************************************************

Other lemmas

************************************************)

Lemma lower_andp_val:
  forall (P Q: val->mpred) v, 
  ((P && Q) v) = (P v && Q v).
Proof. reflexivity. Qed.

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

Lemma data_at_conflict: forall sh t v v' p,
  0 < sizeof t < Int.modulus ->
  data_at sh t v p * data_at sh t v' p |-- FF.
Proof.
  intros.
  eapply derives_trans.
  + apply sepcon_derives.
    apply data_at_data_at_; assumption.
    apply data_at_data_at_; assumption.
  + destruct (nested_non_volatile_type t) eqn:HH.
    - rewrite data_at__memory_block by (auto; omega).
      normalize.
      apply memory_block_conflict; (unfold Int.max_unsigned; omega).
    - unfold data_at_.
      eapply derives_trans; [apply sepcon_derives; apply data_at_non_volatile|].
      rewrite sepcon_prop_prop.
      rewrite HH.
      normalize.
      inversion H0.
Qed.

Lemma field_at_conflict: forall sh t fld p v v',
  0 < sizeof (nested_field_type2 t fld) < Int.modulus ->
  legal_alignas_type t = true ->
  field_at sh t fld v p * field_at sh t fld v' p|-- FF.
Proof.
  intros.
  repeat (rewrite field_at_data_at; try assumption).
  repeat rewrite lower_andp_val.
  repeat (rewrite at_offset'_eq; [|rewrite <- data_at_offset_zero; reflexivity]).
  normalize.
  apply data_at_conflict; try assumption.
Qed.

Lemma field_at__conflict:
  forall sh t fld p,
  0 < sizeof (nested_field_type2 t fld) < Int.modulus ->
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

Hint Extern 1 (isptr _) => (eapply field_compatible_offset_isptr; eassumption).
Hint Extern 1 (isptr _) => (eapply field_compatible0_offset_isptr; eassumption).

Lemma is_pointer_or_null_field_address_lemma:
 forall t path p,
   is_pointer_or_null (field_address t path p) =
   field_compatible t path p.
Proof.
intros.
unfold field_address.
if_tac; apply prop_ext; intuition.
Qed.

Lemma isptr_field_address_lemma:
 forall t path p,
   isptr (field_address t path p) =
   field_compatible t path p.
Proof.
intros.
unfold field_address.
if_tac; apply prop_ext; intuition.
Qed.

Hint Rewrite is_pointer_or_null_field_address_lemma : entailer_rewrite.
Hint Rewrite isptr_field_address_lemma : entailer_rewrite.

