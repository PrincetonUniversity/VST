Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.efield_lemmas.
Require Import floyd.mapsto_memory_block.
Require Import floyd.reptype_lemmas.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.stronger.
Require Import floyd.entailer.
Require Import floyd.closed_lemmas.
Require Import floyd.proj_reptype_lemmas.
Require Import floyd.replace_refill_reptype_lemmas.
Import DataCmpNotations.

Local Open Scope logic.

(*
Definition precise : mpred -> Prop := msl.predicates_sl.precise.

Lemma mapsto_precise: forall sh t v p, precise (mapsto sh t p v).
Proof.
Admitted.

Lemma emp_precise: precise emp.
Proof.
Admitted.

Lemma precise_sepcon: forall P Q, precise P -> precise Q -> precise (P * Q).
Proof.
Admitted.

Lemma precise_andp: forall P Q, precise P -> precise Q -> precise (P && Q).
Proof.
Admitted.

Lemma precise_prop_andp: forall P Q, precise Q -> precise (!! P && Q).
Proof.
Admitted.

Lemma precise_wand_sepcon: forall P Q, precise P -> P -* (P * Q) = Q.
Proof.
Admitted.

Lemma precise_sepcon_cancel: forall P Q R, precise P -> P * Q = P * R -> Q = R.
Proof.
  intros.
  rewrite <- precise_wand_sepcon with (P:= P) (Q := Q) by auto.
  rewrite <- precise_wand_sepcon with (P:= P) (Q := R) by auto.
  rewrite H0.
  reflexivity.
Qed.

(* Here, this precise can be set to be more stronger property, such as splittable precise. *)
Lemma mapsto__precise: forall sh t p, precise (mapsto_ sh t p).
Proof.
  intros.
  unfold mapsto_.
  apply mapsto_precise.
Qed.

Lemma FF_precise: precise (FF).
Proof.
  replace (@FF mpred Nveric) with (mapsto Tsh tint Vundef Vundef).
  apply mapsto_precise.
  unfold mapsto.
  reflexivity.
Qed.

Lemma memory_block_precise: forall sh n p, precise (memory_block sh n p).
Proof.
  intros.
Transparent memory_block.
  unfold memory_block.
Opaque memory_block.
  destruct p; try apply FF_precise.
  apply precise_prop_andp.
  forget (nat_of_Z (Int.unsigned n)) as nn; clear n.
  forget (Int.unsigned i) as ii; clear i.
  generalize ii.
  induction nn; intros.
  + apply emp_precise.
  + simpl. 
    apply precise_sepcon.
    apply mapsto_precise.
    apply IHnn.
Qed.

Lemma at_offset'_preserve_precise: forall P, (forall p, precise (P p)) -> 
  forall be p, P (offset_val (Int.repr 0) p) = P p -> precise (at_offset' P be p).
Proof.
  intros.
  rewrite at_offset'_eq by auto.
  apply H.
Qed.

Lemma spacer_precise: forall sh be ed p, precise (spacer sh be ed p).
Proof.
  intros.
  unfold spacer.
  if_tac.
  apply emp_precise.
  apply at_offset'_preserve_precise; [intros; apply memory_block_precise |].
  apply memory_block_offset_zero.
Qed.

Lemma withspacer_preserve_precise: forall sh be ed P p,
  precise (P p) -> precise (withspacer sh be ed P p).
Proof.
  intros.
  rewrite withspacer_spacer.
Opaque spacer.
  simpl.
Transparent spacer.
  apply precise_sepcon.
  apply spacer_precise.
  exact H.
Qed.

Lemma array_at'_preserve_precise: forall t sh P v lo hi p,
  (forall v p, precise (P v p)) -> precise (array_at' t sh P v lo hi p).
Proof.
  intros.
  unfold array_at'.
  apply precise_prop_andp.
  unfold rangespec.
  forget (nat_of_Z (hi - lo)) as nn; clear hi.
  generalize lo.
  induction nn; intros; simpl.
  + apply emp_precise.
  + apply precise_sepcon.
    apply H.
    apply IHnn.
Qed.

Lemma data_at'_precise: forall sh env t ofs v p, precise (data_at' sh env t ofs v p).
Proof.
  intros.
  apply (type_mut (fun t => forall ofs v p, precise (data_at' sh env t ofs v p))
                  (fun tl => True)
                  (fun fld => (forall al ofs v p, precise (sfieldlist_at' sh env fld al ofs v p)) /\
                              (forall al ofs v p, precise (ufieldlist_at' sh env fld al ofs v p))));
  intros; auto; try simpl;
  try (unfold at_offset2; apply at_offset'_preserve_precise;
       [| try (apply memory_block_offset_zero);
          try (apply mapsto_offset_zero);
          try (symmetry; apply array_at'_offset_zero)]).
  + apply memory_block_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + apply mapsto_precise.
  + intros; apply array_at'_preserve_precise.
    apply H.
  + apply memory_block_precise.
  + destruct H as [H _]; apply H.
  + destruct H as [_ H]; apply H.
  + apply mapsto_precise.
  + simpl; split; intros; apply precise_prop_andp, emp_precise.
  + destruct H0.
    split; intros; destruct (is_Fnil f).
    - apply withspacer_preserve_precise, H.
    - apply precise_sepcon.
      apply withspacer_preserve_precise, H.
      apply H0.
    - apply withspacer_preserve_precise, H.
    - destruct v0.
      apply withspacer_preserve_precise, H.
      apply H1.
Qed.

Lemma data_at_precise: forall sh t v p, precise (data_at sh t v p).
Proof.
  intros; unfold data_at.
  simpl.
  apply precise_prop_andp, data_at'_precise.
Qed.

Lemma field_at_precise: forall sh t gfs v p, precise (field_at sh t gfs v p).
Proof.
  intros; unfold field_at.
  simpl.
  apply precise_prop_andp, data_at'_precise.
Qed.
*)

(******************************************

Lemmas about force_lengthn

******************************************)
(*
Lemma force_lengthn_length_n: forall {A} n (xs : list A) (default: A),
  length (force_lengthn n xs default) = n.
Proof.
  intros.
  revert xs; induction n; intros.
  + reflexivity.
  + simpl.
    destruct xs; simpl; rewrite IHn; reflexivity.
Qed.

Lemma nth_force_lengthn_nil: forall {A} n i (default: A),
  nth i (force_lengthn n nil default) default = default.
Proof.
  intros.
  revert i; induction n; intros.
  + simpl. destruct i; reflexivity.
  + simpl. destruct i.
    - reflexivity.
    - rewrite IHn. reflexivity.
Qed.

Lemma nth_force_lengthn: forall {A} n i (xs : list A) (default: A),
  (0 <= i < n) %nat ->
  nth i (force_lengthn n xs default) default = nth i xs default.
Proof.
  intros.
  revert i H xs; induction n; intros.
  + omega.
  + simpl.
    destruct xs.
    - simpl.
      destruct i; [reflexivity |].
      apply nth_force_lengthn_nil.
    - simpl.
      destruct i; [reflexivity |].
      apply IHn.
      omega.
Qed.

Lemma force_lengthn_id: forall {A} n ct (d: A), length ct = n -> force_lengthn n ct d = ct.
Proof.
  intros.
  revert ct H; induction n; intros.
  + destruct ct; try solve [inversion H].
    reflexivity.
  + destruct ct; try solve [inversion H].
    simpl.
    rewrite IHn by auto.
    reflexivity.
Qed.

Lemma equal_data_one_more_on_list: forall t n a (ct: list (reptype t)) i v,
  legal_alignas_type (Tarray t n a) = true ->
  i < n ->
  Zlength ct = i ->
  (upd_reptype (Tarray t n a) (ArraySubsc i :: nil) ct v) === (ct ++ (v::nil)).
Proof.
  intros.
  apply data_equal_array_ext.
  intros.
  unfold Znth.
  if_tac; [omega |].
  simpl.
  unfold upd_reptype_array, eq_rect_r; simpl.
  assert (i >= 0) by (rewrite Zlength_correct in H1; omega).
  apply Zlength_length in H1; [| omega].
  rewrite force_lengthn_id by auto.
  rewrite skipn_short by (rewrite Z2Nat.inj_add by omega; omega).
  apply data_equal_refl.
Qed.
*)
(******************************************

Proof of field_except lemma

******************************************)
(*
Definition array_aux_field_except: forall sh t gfs t0 n a i,
  legal_alignas_type t = true ->
  nested_field_type2 t gfs = Tarray t0 n a ->
  0 <= i < n ->
  sigT (fun P =>
    forall v v0,
    data_at' sh type_id_env.empty_ti (Tarray t0 n a)
      (nested_field_offset2 t gfs) (upd_reptype_array t0 i v v0) =
    data_at' sh type_id_env.empty_ti t0
      (nested_field_offset2 t (ArraySubsc i ::gfs)) v0 *
    P (proj_except_reptype_array t0 n a i v)).
Proof.
  intros.
  unfold ArrayField, proj_except_reptype_array.
  destruct (i =? 0) eqn:?H; [| destruct (i =? (n - 1)) eqn:?H].
  + rewrite Z.eqb_eq in H2.
    subst.
    change (reptype_structlist
       (all_fields_except_one2
          (Fcons 1002%positive Tvoid
             (Fcons 1003%positive (Tarray t0 (n - 1) a) Fnil)) 1002%positive)) with
       (reptype_structlist
         (Fcons 1003%positive (Tarray t0 (n - 1) a) Fnil)).
    exists (array_at' sh t0 (0 + 1) n (data_at' sh type_id_env.empty_ti t0)
             (nested_field_offset2 t gfs)).
    intros.
    erewrite nested_field_offset2_Tarray by eauto.
    simpl data_at'.
    rewrite split_array_at'_hd by omega.
    reflexivity. (* Coq is crazy. It just got solved *)
  + rewrite Z.eqb_eq in H3.
    subst.
    change (reptype_structlist
       (all_fields_except_one2
          (Fcons 1001%positive (Tarray t0 (n - 1) a)
             (Fcons 1002%positive Tvoid Fnil)) 1002%positive)) with
       (reptype_structlist
         (Fcons 1001%positive (Tarray t0 (n - 1) a) Fnil)).
    exists (array_at' sh t0 0 (n - 1) (data_at' sh type_id_env.empty_ti t0)
             (nested_field_offset2 t gfs)).
    intros.
    erewrite nested_field_offset2_Tarray by eauto.
    simpl data_at'.
    rewrite split_array_at'_tl by omega.
    f_equal.
    - f_equal.
      unfold Znth, upd_reptype_array.
      if_tac; [omega |].
      rewrite app_nth2; [| rewrite force_lengthn_length_n; unfold nat_of_Z; rewrite Z.sub_0_r; omega].
      rewrite force_lengthn_length_n.
      rewrite Z.sub_0_r; rewrite minus_diag.
      reflexivity.
    - unfold array_at', rangespec.
      extensionality p.
      f_equal.
      apply rangespec'_ext.
      intros.
      f_equal.
      unfold Znth, upd_reptype_array.
      if_tac; [omega |].
      rewrite Z2Nat.id in H3 by omega.
      rewrite app_nth1; [| rewrite force_lengthn_length_n; apply Z2Nat.inj_lt; omega].
      rewrite nth_force_lengthn by (split; [|apply Z2Nat.inj_lt]; omega).
      reflexivity.
  + change (reptype_structlist
       (all_fields_except_one2
          (Fcons 1001%positive (Tarray t0 i a)
             (Fcons 1002%positive Tvoid
                (Fcons 1003%positive (Tarray t0 (n - i - 1) a) Fnil)))
          1002%positive)) with
       (reptype_structlist
         (Fcons 1001%positive (Tarray t0 i a)
             (Fcons 1003%positive (Tarray t0 (n - i - 1) a) Fnil))).
    exists (fun v => array_at' sh t0 0 i (data_at' sh type_id_env.empty_ti t0)
             (nested_field_offset2 t gfs) (fst v) *
               array_at' sh t0 (i + 1) n (data_at' sh type_id_env.empty_ti t0)
                (nested_field_offset2 t gfs) (snd v)).
    intros.
    simpl data_at'.
    rewrite split3_array_at' with (mid := i) by omega.
    rewrite <- sepcon_assoc.
    rewrite (sepcon_comm (data_at' _ _ _ _ _)).
    f_equal; [f_equal |].
    - unfold upd_reptype_array, fst.
      unfold array_at', rangespec.
      extensionality p.
      f_equal.
      apply rangespec'_ext.
      intros.
      f_equal.
      unfold Znth, upd_reptype_array.
      if_tac; [omega |].
      rewrite Z2Nat.id in H4 by omega.
      rewrite app_nth1; [| rewrite force_lengthn_length_n; apply Z2Nat.inj_lt; omega].
      rewrite nth_force_lengthn by (split; [|apply Z2Nat.inj_lt]; omega).
      reflexivity.
    - erewrite nested_field_offset2_Tarray by eauto.
      f_equal.
      unfold Znth, upd_reptype_array.
      if_tac; [omega |].
      rewrite Z.sub_0_r; unfold nat_of_Z.
      rewrite app_nth2; [| rewrite force_lengthn_length_n; omega].
      rewrite force_lengthn_length_n.
      rewrite minus_diag.
      reflexivity.
    - unfold upd_reptype_array, snd.
      unfold array_at', rangespec.
      extensionality p.
      f_equal.
      apply rangespec'_ext.
      intros.
      f_equal.
      unfold Znth, upd_reptype_array.
      if_tac; [omega |].
      rewrite Z2Nat.id in H4 by omega.
      rewrite nth_skipn.
      rewrite app_nth2.
      Focus 2. {
        rewrite force_lengthn_length_n.
        rewrite <- Z2Nat.inj_add by omega.
        replace (i0 - (i + 1) + (i - 0 + 1)) with i0 by omega.
        assert (i <= i0) by omega.
        apply Z2Nat.inj_le in H6; [| omega | omega].
        unfold nat_of_Z; omega.
      } Unfocus.
      rewrite force_lengthn_length_n.
      replace (Z.to_nat (i0 - (i + 1)) + nat_of_Z (i - 0 + 1) - nat_of_Z i)%nat with
        (S (Z.to_nat (i0 - (i + 1)))).
      Focus 2. {
        rewrite <- Z2Nat.inj_add by omega.
        rewrite <- Z2Nat.inj_sub by omega.
        replace (i0 - (i + 1) + (i - 0 + 1) - i) with (1 + (i0 - (i + 1))) by omega.
        rewrite Z2Nat.inj_add by omega.
        reflexivity.
      } Unfocus.
      reflexivity.
Defined.

Definition struct_aux_field_except: forall sh t gfs i0 f a i,
  legal_alignas_type t = true ->
  nested_field_type2 t gfs = Tstruct i0 f a ->
  isOK (field_type i f) = true ->
  sigT (fun P =>
    forall v v0,
    data_at' sh type_id_env.empty_ti (Tstruct i0 f a)
      (nested_field_offset2 t gfs) (upd_reptype_structlist f i 0 v v0) =
    data_at' sh type_id_env.empty_ti _
      (nested_field_offset2 t (StructField i ::gfs)) v0 *
    P (proj_except_reptype_structlist f i v)).
Proof.
  intros.
  admit.
Qed.

Definition union_aux_field_except: forall sh t gfs i0 f a i,
  legal_alignas_type t = true ->
  nested_field_type2 t gfs = Tunion i0 f a ->
  isOK (field_type i f) = true ->
  sigT (fun P =>
    forall v0,
    data_at' sh type_id_env.empty_ti (Tunion i0 f a)
      (nested_field_offset2 t gfs) (upd_reptype_unionlist f i v0) =
    data_at' sh type_id_env.empty_ti _
      (nested_field_offset2 t (UnionField i ::gfs)) v0 *
    P (proj_except_reptype_unionlist)).
Proof.
  intros.
  admit.
Defined.

Definition field_except_at_1_lemma: forall sh t gf gfs,
  legal_nested_field t (gf :: gfs) ->
  sigT (fun P => forall v v0 v0',
    JMeq v0 v0' ->
    field_at sh t gfs (upd_reptype _ (gf :: nil) v v0) =
      field_at sh t (gf :: gfs) v0' *
        P (proj_except_reptype _ gf nil v)).
Proof.
  intros.
  unfold field_at.
  cut (legal_alignas_type t = true ->
       sigT (fun P => forall v v0 v0',
         JMeq v0 v0' ->
         data_at' sh type_id_env.empty_ti (nested_field_type2 t gfs)
           (nested_field_offset2 t gfs)
           (upd_reptype (nested_field_type2 t gfs) (gf :: nil) v v0) =
         data_at' sh type_id_env.empty_ti (nested_field_type2 t (gf :: gfs))
           (nested_field_offset2 t (gf :: gfs)) v0' *
         P (proj_except_reptype (nested_field_type2 t gfs) gf nil v))).
  Focus 1. {
    intros ?H.
    destruct (legal_alignas_type t) eqn:?H.
    + destruct H0 as [P ?H]; [reflexivity |].
      exists P.
      intros.
      specialize (H0 v v0 v0' H2).
      rewrite H0.
      assert (legal_nested_field t gfs) by (solve_legal_nested_field_cons H; auto).
      extensionality p.
      apply pred_ext; simpl; normalize.
    + exists (fun _ => TT).
      intros.
      extensionality p.
      simpl.
      replace (@prop mpred Nveric (false = true)) with (@FF mpred Nveric)
        by (apply pred_ext; normalize; congruence).
      normalize.
  } Unfocus.
  intros.
  solve_legal_nested_field_cons H.
Opaque data_at'.
  + unfold upd_reptype, proj_except_reptype_array; simpl.
    unfold eq_rect_r, eq_rect, nested_field_type2_nil; simpl.
Transparent data_at'.
    rewrite (nested_field_type2_Tarray t0 z a gfs t i Heq0).
    destruct (array_aux_field_except sh t gfs t0 z a i) as [P ?H]; auto.
    exists P.
    change (nested_field_type2 (Tarray t0 z a) (ArraySubsc i :: nil)) with t0.
    intros.
    subst v0.
    apply H3.
  + admit.
  + admit.
Defined.

Definition field_except_at_lemma_aux: forall sh t gf gfs0 gfs1,
  legal_nested_field t (gf :: gfs1 ++ gfs0) ->
  sigT (fun P => forall v v0 v0',
    JMeq v0 v0' ->
    field_at sh t gfs0 (upd_reptype _ (gf :: gfs1) v v0) =
      field_at sh t (gf :: gfs1 ++ gfs0) v0' *
        P (proj_except_reptype _ gf gfs1 v)).
Proof.
  intros.
  revert gf H; induction gfs1; intros.
  + simpl app in H |- *.
    apply field_except_at_1_lemma; auto.
  + destruct (IHgfs1 a) as [P0 ?H];
      [simpl app in H; clear - H; solve_legal_nested_field_cons H; auto |].
    destruct (field_except_at_1_lemma sh t gf (a :: gfs1 ++ gfs0))
       as [P1 ?H]; [exact H |].
    destruct (proj_except_reptype_cons_is_pair (nested_field_type2 t gfs0)
                gf a gfs1) as [F [G ?H]];
      [apply legal_nested_field_app', H |].
    exists (fun v => P0 (fst (F v)) *
      P1 (eq_rect_r (fun t => reptype (nf_sub2 t gf nil)) (snd (F v))
        (eq_sym (nested_field_type2_nested_field_type2 _ _ _)))).
    intros.

    erewrite upd_reptype_cons;
      [| apply legal_nested_field_app', H |].
    Focus 2. {
      instantiate (1 := eq_rect_r reptype v0
                          (nested_field_type2_nested_field_type2
                            (nested_field_type2 t gfs0) (a :: gfs1) (gf :: nil))).
      apply JMeq_sym, eq_rect_r_JMeq.
    } Unfocus.
    (* Step 1 finish. *)

    rewrite !(proj1 (H2 _)); clear F G H2.
    unfold fst, snd.
    (* Step 2 finish. *)

    erewrite H0.
    Focus 2. {
      apply JMeq_sym.
      apply eq_rect_r_JMeq with
        (F := reptype)
        (H := eq_sym (nested_field_type2_nested_field_type2 t gfs0 (a :: gfs1))).
    } Unfocus.
    rewrite (sepcon_comm (P0 _)), <- sepcon_assoc.
    f_equal.
    clear P0 H0.
    (* Step 3 finish *)

    match goal with
    | |- appcontext [upd_reptype _ _ ?V ?V0] =>
           replace (eq_rect_r reptype (upd_reptype _ _ V V0)
                     (eq_sym (nested_field_type2_nested_field_type2 t gfs0 (a :: gfs1))))
           with (upd_reptype (nested_field_type2 t (a :: gfs1 ++ gfs0)) (gf :: nil)
             (eq_rect_r reptype V
                 (eq_sym (nested_field_type2_nested_field_type2 t gfs0 (a :: gfs1))))
             (eq_rect_r (fun t0 : type => reptype (nested_field_type2 t0 (gf :: nil))) V0
                 (eq_sym (nested_field_type2_nested_field_type2 t gfs0 (a :: gfs1)))));
             [| forget V as r; forget V0 as r0]
    end.
    Focus 2. {
      apply JMeq_eq, JMeq_sym.
      eapply JMeq_trans; [apply eq_rect_r_JMeq |].
      forget (eq_sym (nested_field_type2_nested_field_type2 t gfs0 (a :: gfs1))) as HH.
      revert r r0 HH.
      rewrite nested_field_type2_nested_field_type2.
      intros.
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      reflexivity.
    } Unfocus.
    erewrite H1.
    Focus 2. {
      eapply JMeq_trans; [apply eq_rect_r_JMeq with (F := (fun t0 : type => reptype (nested_field_type2 t0 (gf :: nil))))|].
      eapply JMeq_trans; [apply eq_rect_r_JMeq |].
      apply JMeq_sym.
      instantiate (1 := eq_rect_r reptype v0 (eq_sym (nested_field_type2_nested_field_type2 _ _ _))).
      apply eq_rect_r_JMeq.
    } Unfocus.
    f_equal.
    (* Step 4 finish *)

    - f_equal.
      apply JMeq_eq.
      eapply JMeq_trans; [apply eq_rect_r_JMeq |].
      exact H3.
    - f_equal.
      forget (eq_sym (nested_field_type2_nested_field_type2 t gfs0 (a :: gfs1))) as HH.
      forget (proj_reptype (nested_field_type2 t gfs0) (a :: gfs1) v) as r.
      revert r HH.
      rewrite nested_field_type2_nested_field_type2.
      intros.
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      reflexivity.
Defined.
*)

Section DATA_AT_WITH_HOLES.

Context {cs: compspecs}.

Definition data_at'_with_holes (sh: Share.t) t h (v: reptype_with_holes t h) (p: val) : mpred.
  admit.
Defined.

Definition holes_at (sh: Share.t) t (h: holes) (v: holes_subs t) (p: val) : mpred.
  admit.
Defined.

Lemma holes_at_lemma: forall sh t h v v0 p,
  legal_holes t h ->
  data_at' sh t (refill_reptype v v0) p =
  data_at'_with_holes sh t h v p * holes_at sh t h v0 p.
Admitted.

(*
Lemma upd_stronger: forall t gfs v v0 v1,
  legal_nested_field t gfs ->
  v0 >>> v1 ->
  upd_reptype t gfs v v0 >>> upd_reptype t gfs v v1.
Proof.
  intros.
  intros sh p.
  destruct gfs.
  + simpl.
    apply H0.
  + rewrite !field_except_at_data_at by auto.
    simpl.
    cancel.
    rewrite !field_at_data_at.
    apply H0.
Qed.

Lemma Z2Nat_nonpos_0: forall z, z <= 0 -> Z.to_nat z = 0%nat.
Proof.
  intros.
  destruct z.
  + reflexivity.
  + pose proof Zgt_pos_0 p.
    omega.
  + reflexivity.
Qed.

Lemma array_at_emp:
  forall sh t gfs lo hi v p, lo >= hi ->
    array_at sh t gfs lo hi v p = !! field_compatible t gfs p && emp.
Proof.
  intros. unfold array_at, rangespec, field_compatible.
  replace (nat_of_Z (hi - lo)) with 0%nat.
  + simpl. apply pred_ext; normalize.
  + rewrite Z2Nat_nonpos_0 by omega.
    reflexivity.
Qed.

Lemma data_at_Tarray_split3: forall sh t n a i v,
  0 <= i < n ->
  data_at sh (Tarray t n a) v = 
    data_at sh (Tarray t n a) (force_lengthn (nat_of_Z i) v (default_val _) ++
      (Znth i v (default_val _)) :: skipn (nat_of_Z (i + 1)) v).
Proof.
  intros.
  apply data_at_Tarray_ext.
  intros j ?H.
  unfold Znth.
  if_tac; [omega |].
  if_tac; [omega |].
  unfold nat_of_Z.
  destruct (Z_dec i j) as [[? | ?] | ?].
  + assert ((Z.to_nat i < Z.to_nat j)%nat) by (apply Z2Nat.inj_lt in l; omega).
    rewrite app_nth2 by (rewrite force_lengthn_length_n; omega).
    rewrite force_lengthn_length_n.
    simpl.
    destruct ((Z.to_nat j - Z.to_nat i)%nat) eqn:?H; [omega |].
    rewrite nth_skipn.
    f_equal.
    f_equal.
    change (i + 1) with (Z.succ i).
    rewrite Z2Nat.inj_succ by omega.
    omega.
  + assert ((Z.to_nat j < Z.to_nat i)%nat) by (apply Z2Nat.inj_lt; omega).
    rewrite app_nth1 by (rewrite force_lengthn_length_n; omega).
    rewrite nth_force_lengthn by omega.
    reflexivity.
  + subst.
    rewrite app_nth2 by (rewrite force_lengthn_length_n; omega).
    rewrite force_lengthn_length_n.
    rewrite minus_diag.
    simpl.
    reflexivity.
Qed.

Lemma stronger_upd_self: forall t gfs v,
  legal_nested_field t gfs ->
  v >>> (upd_reptype t gfs v (proj_reptype t gfs v)).
Proof.
  intros.
  induction gfs as [| gf gfs].
  + intros sh p. simpl. auto.
  + assert (legal_nested_field t gfs) by (solve_legal_nested_field_cons H; auto).
Opaque eq_rect_r.
    simpl upd_reptype; simpl proj_reptype.
    eapply stronger_trans; [apply IHgfs, H0 |].
    apply upd_stronger; auto.
    generalize (proj_reptype t gfs v).
    generalize ((nested_field_type2_cons t gf gfs)).
    solve_legal_nested_field_cons H.
    - simpl; intros.
      unfold upd_reptype_array.
      rewrite eq_rect_r_eq_rect_r_eq_sym.
      intros sh p.
      rewrite <- data_at_Tarray_split3; auto.
    - simpl; intros.
      unfold upd_reptype_array.
      rewrite eq_rect_r_eq_rect_r_eq_sym.
      intros sh p.
      admit.
    - simpl; intros.
      unfold upd_reptype_array.
      rewrite eq_rect_r_eq_rect_r_eq_sym.
      intros sh p.
      admit.
Qed.
*)


    
















(*

Lemma is_Fnil_fieldlist_app:
  forall f1 f2, is_Fnil (fieldlist_app f1 f2) = true -> is_Fnil f1 = true /\ is_Fnil f2 = true.
Proof.
  intros.
  destruct f1, f2; simpl in *; auto.
Qed.

Fixpoint reptype_suf_struct {fp fs: fieldlist} (v: reptype_structlist (fieldlist_app fp fs)) (vs: reptype_structlist fs) :=
  match fp as fp'
    return reptype_structlist (fieldlist_app fp' fs) -> Prop
  with
  | Fnil => fun v => v = vs
  | Fcons i0 t0 fp0 => 
    if (is_Fnil (fieldlist_app fp0 fs)) as b
      return (if b then reptype t0 else reptype t0 * reptype_structlist (fieldlist_app fp0 fs)) -> Prop
    then fun _ => True
    else fun v => reptype_suf_struct (snd v) vs
  end v.

Lemma reptype_suf_struct_Fnil: forall {f} (v: reptype_structlist f), exists v0, @reptype_suf_struct Fnil f v0 v /\ JMeq v0 v.
Proof.
  intros.
  simpl in v |- *.
  eauto.
Qed.

Lemma reptype_suf_struct_Fcons: forall f0 i0 t1 i1 t2 f v v0, @reptype_suf_struct f0 (Fcons i0 t1 (Fcons i1 t2 f)) v v0 -> exists v1, JMeq v v1 /\ @reptype_suf_struct (fieldlist_app f0 (Fcons i0 t1 Fnil)) (Fcons i1 t2 f) v1 (snd v0).
Proof.
  intros.
  induction f0.
  + simpl in *.
    exists v.
    rewrite H; auto.
  + simpl in v, H |- *.
    revert v H.
    destruct (is_Fnil (fieldlist_app f0 (Fcons i0 t1 (Fcons i1 t2 f)))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb.
      destruct Heqb as [_ H].
      inversion H.
    } Unfocus.
    destruct (is_Fnil (fieldlist_app (fieldlist_app f0 (Fcons i0 t1 Fnil))
                  (Fcons i1 t2 f))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb0.
      destruct Heqb0 as [_ H0].
      inversion H0.
    } Unfocus.
    intros.
    destruct (IHf0 (snd v) H) as [v2 [? ?]].
    exists (fst v, v2).
    split.
    - clear H1; revert v2 H0.
      rewrite <- fieldlist_app_Fcons.
      intros.
      rewrite <- H0.
      destruct v; reflexivity.
    - simpl.
      exact H1.
Qed.

Lemma proj_reptype_structlist_ofs: forall i f ofs ofs0 v,
  JMeq (proj_reptype_structlist i f ofs v) (proj_reptype_structlist i f ofs0 v).
Proof.
  intros.
  revert ofs ofs0.
  induction f; intros.
  + reflexivity.
  + simpl.
    if_tac.
    - revert v; simpl; if_tac; reflexivity.
    - revert v; simpl; destruct (is_Fnil f) eqn:?; intros.
      * destruct f; inversion Heqb; reflexivity.
      * apply IHf.
Qed.

Lemma proj_reptype_structlist_fieldlist_app: forall f0 f id t v v0,
  fieldlist_no_replicate (fieldlist_app f0 f) = true ->
  field_type id f = Errors.OK t ->
  @reptype_suf_struct f0 f v v0 ->
  JMeq (proj_reptype_structlist id (fieldlist_app f0 f) 0 v) (proj_reptype_structlist id f 0 v0).
Proof.
  intros.
  generalize 0 at 1 2.
  generalize 0.
  induction f0; intros.
  + simpl in v, H1 |- *.
    rewrite H1.
    apply proj_reptype_structlist_ofs.
  + simpl in H1 |- *.
    if_tac. (* whether id = i *)
    - pose proof (fieldlist_no_replicate_fact _ _ id H).
      simpl in H3.
      if_tac in H3; [| congruence].
      rewrite H0 in H3.
      pose proof H3 eq_refl eq_refl.
      inversion H5.
    - revert v H1; simpl.
      destruct (is_Fnil (fieldlist_app f0 f)) eqn:?; intros. (* whether fieldlist f0 f is Fnil *)
      * destruct (is_Fnil_fieldlist_app _ _ Heqb) as [_ ?].
        destruct f; [inversion H0 | inversion H3].
      * simpl in H.
        rewrite andb_true_iff in H.
        destruct H.
        apply IHf0; auto.
Qed.

Lemma proj_reptype_cons_hd_Tstruct_Fnil: forall i f0 i0 t0 a t id gfs v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t gfs = Tstruct i (fieldlist_app f0 (Fcons i0 t0 Fnil)) a ->
  JMeq (proj_reptype t gfs v) vs ->
  @reptype_suf_struct f0 (Fcons i0 t0 Fnil) vs v0 ->
  JMeq (proj_reptype t (StructField id :: gfs) v) v0.
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t gfs v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ gfs H.
  rewrite H1 in H4.
  simpl in H4.
  apply andb_true_iff in H4; destruct H4 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_structlist_fieldlist_app; eauto.
  + simpl.
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

Lemma proj_reptype_cons_hd_Tstruct_Fcons: forall i f0 i0 t0 i1 t1 f a t id gfs v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t gfs = Tstruct i (fieldlist_app f0 (Fcons i0 t0 (Fcons i1 t1 f))) a ->
  JMeq (proj_reptype t gfs v) vs ->
  @reptype_suf_struct f0 (Fcons i0 t0 (Fcons i1 t1 f)) vs v0 ->
  JMeq (proj_reptype t (StructField id :: gfs) v) (fst v0).
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t gfs v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ gfs H.
  rewrite H1 in H4.
  simpl in H4.
  apply andb_true_iff in H4; destruct H4 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_structlist_fieldlist_app; eauto.
  + simpl.
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

Definition nested_sfieldlist_at_sub: forall sh t id gfs i f a0 p t0,
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t gfs = Tstruct i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v1,
  JMeq (proj_reptype t gfs v) v1 ->  
  field_at sh t gfs (proj_reptype t gfs v) p = 
  field_at sh t (StructField id :: gfs) (proj_reptype t (StructField id :: gfs) v) p * P (proj_except_reptype_structlist f id v1)).
Proof.
  cut (forall sh t id gfs i f a0 p t0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t gfs = Tstruct i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v0 v1,  
  JMeq (proj_reptype t gfs v) v1 ->
  JMeq v0 v1 ->
  nested_sfieldlist_at sh t gfs f v0 p = 
  field_at sh t (StructField id :: gfs) (proj_reptype t (StructField id :: gfs) v) p * 
    P (proj_except_reptype_structlist f id v1))).
  Focus 1. {
    intro H; intros.
    assert (nested_reptype_structlist t gfs f = reptype_structlist f).
      erewrite <- nested_reptype_structlist_lemma2; eauto.
      rewrite H2.
      reflexivity.
    destruct (H sh t id gfs i f a0 p t0 H1 H2 H3) as [PH H5]; clear H.
    eexists; intros.
    pose (eq_rect_r (fun T => T) v1 H4) as v0.
    erewrite field_at_Tstruct; eauto.
    instantiate (2 :=  v0).
    eapply (H5 v v0 v1); eauto.
    + subst v0. apply eq_rect_r_JMeq with (F:=fun T => T).
    + destruct f; [inversion H3 | reflexivity].
    + rewrite H; subst v0. apply JMeq_sym, eq_rect_r_JMeq with (F:=fun T => T).
  } Unfocus.
  intros.
  change f with (fieldlist_app Fnil f) in H0.
  cut (sigT (fun P => forall (v : reptype t) (v0 : nested_reptype_structlist t gfs f)
       (v1 : reptype_structlist f) (vs: reptype_structlist (fieldlist_app Fnil f)),
     JMeq (proj_reptype t gfs v) vs ->
     reptype_suf_struct vs v1 ->
     JMeq v0 v1 ->
     nested_sfieldlist_at sh t gfs f v0 p =
     field_at sh t (StructField id :: gfs) (proj_reptype t (StructField id :: gfs) v) p *
     P (proj_except_reptype_structlist f id v1))).
  Focus 1. {
    intro H2.
    destruct H2 as [P H3]; exists P.
    intros.
    destruct (reptype_suf_struct_Fnil v1) as [x [? ?]].
    eapply H3 with (vs := x); eauto.
    rewrite H6.
    exact H2.
  } Unfocus.
  revert H0.
  generalize Fnil.
  induction f; intros.
  + inversion H1.
  + assert (fieldlist_no_replicate (fieldlist_app f0 (Fcons i0 t1 f)) = true).
    Focus 1. {
      pose proof nested_field_type2_nest_pred eq_refl _ gfs H.
      rewrite H0 in H2.
      simpl in H2.
      apply andb_true_iff in H2.
      tauto.
    } Unfocus.
    assert (reptype (nested_field_type2 t (StructField i0 :: gfs)) = reptype t1)
      by (erewrite nested_field_type2_Tstruct_mid; eauto).
    assert (nested_reptype_structlist t gfs f = reptype_structlist f).
    Focus 1. {
      unfold nested_field_type2 in H0.
      valid_nested_field_rec t gfs H0.
      subst t2.
      rewrite fieldlist_app_Fcons in H4.
      eapply eq_sym, nested_reptype_structlist_lemma; eauto.
    } Unfocus.
    simpl in H1.
    if_tac in H1. (* whether id = the ident of head field *)
    - clear IHf. 
      simpl nested_sfieldlist_at.
Opaque field_at proj_reptype spacer nested_sfieldlist_at.
      destruct f; simpl;
      (if_tac; [| congruence]);
      eexists; intros;
      rewrite withspacer_spacer; simpl.
Transparent field_at proj_reptype spacer nested_sfieldlist_at.
      * pose proof proj_reptype_cons_hd_Tstruct_Fnil i f0 i0 t1 a0 t id gfs v vs v1 H H5 H0 H7 H8.
        subst.
        simpl in H10, H9.
        rewrite <- H10 in H9.
        apply JMeq_eq in H9.
        rewrite H9.
        rewrite sepcon_comm.
        match goal with
        | |- _ * ?T = _ => instantiate (1:= fun _ => T)
        end.
        eauto.
      * rewrite sepcon_comm with (Q := field_at sh t (StructField i0 :: gfs) (fst v0) p).
        rewrite sepcon_assoc.
        
        f_equal.
        Focus 1. {
          pose proof proj_reptype_cons_hd_Tstruct_Fcons i f0 i0 t1 i1 t2 f a0 t id gfs v vs v1 H H5 H0 H7 H8.
          subst; f_equal.
          apply JMeq_eq.
          rewrite H10.
          apply JMeq_fst; eauto.
        } Unfocus.
        Focus 1. {
          match goal with
          | |- ?T * (?R _ _) = _ => instantiate (1:= fun v => T * R (eq_rect_r (fun T => T) v H4) p)
          end.
          simpl.
          f_equal. f_equal.
          apply JMeq_snd in H9; eauto.
          apply eq_sym, JMeq_eq.
          simpl in *; rewrite H9.
          apply (eq_rect_JMeq _ _ _ (fun y => y) (snd v1) (eq_sym H4)).
        } Unfocus.
    - destruct f; try (solve [inversion H1]).
      rewrite fieldlist_app_Fcons in H0.
      destruct (IHf H1 (fieldlist_app f0 (Fcons i0 t1 Fnil)) H0) as [PH IH]; clear IHf.
      cut (sigT (fun P :
            (if is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id) 
             then reptype t1
             else reptype t1 * reptype_structlist (all_fields_except_one2 (Fcons i1 t2 f) id))
             -> mpred =>
             forall (v : reptype t)
             (v0 : nested_reptype_structlist t gfs (Fcons i0 t1 (Fcons i1 t2 f)))
             (v1 : reptype_structlist (Fcons i0 t1 (Fcons i1 t2 f)))
             (vs : reptype_structlist
                     (fieldlist_app f0 (Fcons i0 t1 (Fcons i1 t2 f)))),
             JMeq (proj_reptype t gfs v) vs ->
             reptype_suf_struct vs v1 ->
             JMeq v0 v1 ->
             nested_sfieldlist_at sh t gfs (Fcons i0 t1 (Fcons i1 t2 f)) v0 p =
             field_at sh t (StructField id :: gfs) (proj_reptype t (StructField id :: gfs) v) p *
             P (if is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id) as b
                  return if b 
                         then reptype t1
                         else reptype t1 * reptype_structlist 
                              (all_fields_except_one2 (Fcons i1 t2 f) id)
                then fst v1
                else (fst v1, proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1))))).
      Focus 1. {
        intro H6.
        destruct H6 as [P H6]. 
        simpl (all_fields_except_one2 (Fcons i0 t1 (Fcons i1 t2 f)) id).
        simpl proj_except_reptype_structlist.
        if_tac; [congruence | exists P; intros].
        eapply H6; eauto.
      } Unfocus.
      assert (forall (v0 : nested_reptype_structlist t gfs (Fcons i0 t1 (Fcons i1 t2 f)))
       (v1 : reptype_structlist (Fcons i0 t1 (Fcons i1 t2 f))),
        JMeq v0 v1 -> (JMeq (fst v0) (fst v1) /\ JMeq (snd v0) (snd v1))) by
        (intros; split; [apply JMeq_fst | apply JMeq_snd]; eauto).
      
Opaque field_at proj_reptype spacer nested_sfieldlist_at proj_except_reptype_structlist.
      destruct (is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id)) eqn:HH; eexists; intros;
      replace (nested_sfieldlist_at sh t gfs (Fcons i0 t1 (Fcons i1 t2 f)) v0 p) with
             ((withspacer sh
          (nested_field_offset2 t (StructField i0 :: gfs) +
           sizeof (nested_field_type2 t (StructField i0 :: gfs)))
          (align
             (nested_field_offset2 t (StructField i0 :: gfs) +
              sizeof (nested_field_type2 t (StructField i0 :: gfs))) 
             (alignof_hd (Fcons i1 t2 f))) (field_at sh t (StructField i0 :: gfs) (fst v0)) p *
          nested_sfieldlist_at sh t gfs (Fcons i1 t2 f) (snd v0) p)) by reflexivity;
      rewrite withspacer_spacer; simpl.
Transparent field_at proj_reptype spacer nested_sfieldlist_at proj_except_reptype_structlist.
      * destruct (reptype_suf_struct_Fcons f0 i0 t1 i1 t2 f vs v1 H8) as [v2 [? ?]].
        assert (nested_sfieldlist_at sh t gfs (Fcons i1 t2 f) (snd v0) p =
                field_at sh t (StructField id :: gfs) (proj_reptype t (StructField id :: gfs) v) p *
                PH (proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1))).
        Focus 1. {
          apply (IH v (snd v0) (snd v1) v2); eauto.
          + rewrite <- H10. exact H7.
          + apply JMeq_snd; eauto.
        } Unfocus.
        rewrite H12; clear H12 IH.
        destruct (H6 v0 v1 H9).
        match goal with
        | |- ?A2 * (?A1 _ _) * (_ * _) = _ => 
          instantiate (1:= fun v => A2 * A1 (eq_rect_r (fun T => T) v H3) p * (PH (struct_default_val _)))
        end.
        assert (all_fields_except_one2 (Fcons i1 t2 f) id = Fnil) by
          (destruct (all_fields_except_one2 (Fcons i1 t2 f) id); [trivial | inversion HH]).
        forget (proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1)) as tt'.
        forget (struct_default_val (all_fields_except_one2 (Fcons i1 t2 f) id)) as tt''.
        revert tt' tt'' PH.
        rewrite H14; intros.
        normalize.
        destruct tt', tt''.
        f_equal.
        rewrite sepcon_comm, <- sepcon_assoc.
        f_equal.
        f_equal.
        apply eq_sym, JMeq_eq.
        simpl in *; rewrite H12.
        erewrite eq_rect_JMeq with (F := fun T => T).
        reflexivity.
      * destruct (reptype_suf_struct_Fcons f0 i0 t1 i1 t2 f vs v1 H8) as [v2 [? ?]].
        assert (nested_sfieldlist_at sh t gfs (Fcons i1 t2 f) (snd v0) p =
                field_at sh t (StructField id :: gfs) (proj_reptype t (StructField id :: gfs) v) p *
                PH (proj_except_reptype_structlist (Fcons i1 t2 f) id (snd v1))).
        Focus 1. {
          apply (IH v (snd v0) (snd v1) v2); eauto.
          + rewrite <- H10. exact H7.
          + apply JMeq_snd; eauto.
        } Unfocus.
        rewrite H12; clear H12 IH.
        destruct (H6 v0 v1 H9).
        match goal with
        | |- ?A2 * (?A1 _ _) * (_ * _) = _ => 
          instantiate (1:= fun v => A2 * A1 (eq_rect_r (fun T => T) (fst v) H3) p * PH (snd v))
        end.
        normalize.
        f_equal.
        rewrite sepcon_comm, <- sepcon_assoc.
        f_equal.
        f_equal.
        apply eq_sym, JMeq_eq.
        simpl in *; rewrite H12.
        erewrite eq_rect_JMeq with (F := fun T => T).
        reflexivity.
Qed.

Fixpoint reptype_suf_union {fp fs: fieldlist} (v: reptype_unionlist (fieldlist_app fp fs)) (vs: reptype_unionlist fs) :=
  match fp as fp'
    return reptype_unionlist (fieldlist_app fp' fs) -> Prop
  with
  | Fnil => fun v => v = vs
  | Fcons i0 t0 fp0 => 
    if (is_Fnil (fieldlist_app fp0 fs)) as b
      return (if b then reptype t0 else reptype t0 + reptype_unionlist (fieldlist_app fp0 fs)) -> Prop
    then fun _ => True
    else fun v => 
      match v with
      | inl _ => False
      | inr v' => reptype_suf_union v' vs
      end
  end v.

Lemma reptype_suf_union_Fnil: forall {f} (v: reptype_unionlist f), exists v0, @reptype_suf_union Fnil f v0 v /\ JMeq v0 v.
Proof.
  intros.
  simpl in v |- *.
  eauto.
Qed.

Lemma reptype_suf_union_Fcons: forall f0 i0 t1 i1 t2 f v v0, @reptype_suf_union f0 (Fcons i0 t1 (Fcons i1 t2 f)) v v0 -> exists v1, JMeq v v1 /\ (forall v2: reptype_unionlist (Fcons i1 t2 f), v0 = inr v2 -> @reptype_suf_union (fieldlist_app f0 (Fcons i0 t1 Fnil)) (Fcons i1 t2 f) v1 v2).
Proof.
  intros.
  induction f0.
  + simpl in *.
    exists v.
    split; [rewrite H | intros; subst]; auto.
  + simpl in v, H |- *.
    revert v H.
    destruct (is_Fnil (fieldlist_app f0 (Fcons i0 t1 (Fcons i1 t2 f)))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb.
      destruct Heqb as [_ H].
      inversion H.
    } Unfocus.
    destruct (is_Fnil (fieldlist_app (fieldlist_app f0 (Fcons i0 t1 Fnil))
                  (Fcons i1 t2 f))) eqn:?.
    Focus 1. {
      apply is_Fnil_fieldlist_app in Heqb0.
      destruct Heqb0 as [_ H0].
      inversion H0.
    } Unfocus.
    intros.
    destruct v as [v | v]; [inversion H |].
    destruct (IHf0 v H) as [v2 [? ?]].
    exists (inr v2).
    split.
    - rewrite H0. reflexivity.
    - simpl.
      exact H1.
Qed.

Lemma proj_reptype_unionlist_fieldlist_app: forall f0 f id t v v0,
  fieldlist_no_replicate (fieldlist_app f0 f) = true ->
  field_type id f = Errors.OK t ->
  @reptype_suf_union f0 f v v0 ->
  JMeq (proj_reptype_unionlist id (fieldlist_app f0 f) v) (proj_reptype_unionlist id f v0).
Proof.
  intros.
  induction f0.
  + simpl in v, H1 |- *.
    rewrite H1.
    reflexivity.
  + simpl in H1 |- *.
    if_tac. (* whether id = i *)
    - pose proof (fieldlist_no_replicate_fact _ _ id H).
      simpl in H3.
      if_tac in H3; [| congruence].
      rewrite H0 in H3.
      pose proof H3 eq_refl eq_refl.
      inversion H5.
    - revert v H1; simpl.
      destruct (is_Fnil (fieldlist_app f0 f)) eqn:?; intros. (* whether fieldlist f0 f is Fnil *)
      * destruct (is_Fnil_fieldlist_app _ _ Heqb) as [_ ?].
        destruct f; [inversion H0 | inversion H3].
      * simpl in H.
        rewrite andb_true_iff in H.
        destruct H.
        destruct v as [v | v]; [inversion H1 |].
        apply IHf0; auto.
Qed.

Lemma proj_reptype_cons_hd_Tunion_Fnil: forall i f0 i0 t0 a t id gfs v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t gfs = Tunion i (fieldlist_app f0 (Fcons i0 t0 Fnil)) a ->
  JMeq (proj_reptype t gfs v) vs ->
  @reptype_suf_union f0 (Fcons i0 t0 Fnil) vs v0 ->
  JMeq (proj_reptype t (UnionField id :: gfs) v) v0.
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t gfs v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ gfs H.
  rewrite H1 in H4.
  simpl in H4.
  apply andb_true_iff in H4; destruct H4 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_unionlist_fieldlist_app; eauto.
  + simpl.
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

Lemma proj_reptype_cons_hd_Tunion_Fcons: forall i f0 i0 t0 i1 t1 f a t id gfs v vs v0,
  nested_legal_fieldlist t = true ->
  id = i0 ->
  nested_field_type2 t gfs = Tunion i (fieldlist_app f0 (Fcons i0 t0 (Fcons i1 t1 f))) a ->
  JMeq (proj_reptype t gfs v) vs ->
  @reptype_suf_union f0 (Fcons i0 t0 (Fcons i1 t1 f)) vs v0 ->
  forall v0', v0 = inl v0' ->
  JMeq (proj_reptype t (UnionField id :: gfs) v) v0'.
Proof.
  intros.
  simpl.
  rewrite nested_field_type2_cons.
  revert H2.
  generalize (proj_reptype t gfs v) as v2.
  rewrite H1.
  intros.
  clear v.
  rewrite <- eq_rect_eq.
  pose proof nested_field_type2_nest_pred (eq_refl) _ gfs H.
  rewrite H1 in H5.
  simpl in H5.
  apply andb_true_iff in H5; destruct H5 as [? _].
  simpl in v2, H2.
  apply JMeq_eq in H2.
  subst.
  unfold field_offset. (* in implicit argument of JMeq *)
  erewrite proj_reptype_unionlist_fieldlist_app; eauto.
  + simpl;
    if_tac; [reflexivity | congruence].
  + simpl;
    if_tac; [reflexivity | congruence].
Qed.

(*
Definition nested_ufieldlist_at_sub: forall sh t id gfs i f a0 p t0,
  legal_alignas_type t = true ->
  nested_legal_fieldlist t = true ->
  nested_field_type2 t gfs = Tunion i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v1,
  JMeq (proj_reptype t gfs v) v1 ->
  is_precise_proj_reptype_unionlist f id v1 = true ->
  field_at sh t gfs (proj_reptype t gfs v) p = 
  field_at sh t (id :: gfs) (proj_reptype t (id :: gfs) v) p * P).
Proof.
  cut (forall sh t id gfs i f a0 p t0,
  nested_legal_fieldlist t = true ->
  nested_field_type2 t gfs = Tunion i f a0 ->
  field_type id f = Errors.OK t0 ->
  sigT (fun P => forall v v0 (v1: reptype_unionlist f),  
  JMeq (proj_reptype t gfs v) v1 ->
  JMeq v0 v1 ->
  is_precise_proj_reptype_unionlist f id v1 = true ->
  nested_ufieldlist_at sh t gfs f v0 p = 
  field_at sh t (id :: gfs) (proj_reptype t (id :: gfs) v) p * P)).
  Focus 1. {
    intro H; intros.
    assert (nested_reptype_unionlist t gfs f = reptype_unionlist f).
      erewrite <- nested_reptype_unionlist_lemma2; eauto.
      rewrite H2.
      reflexivity.
    destruct (H sh t id gfs i f a0 p t0 H1 H2 H3) as [PH H5]; clear H.
    eexists; intros.
    pose (eq_rect_r (fun T => T) v1 H4) as v0.
    erewrite field_at_Tunion; eauto.
    instantiate (2 := v0).
    eapply (H5 v v0 v1); eauto.
    + subst v0. apply eq_rect_r_JMeq with (F:=fun T => T).
    + destruct f; [inversion H3 | reflexivity].
    + rewrite H; subst v0. apply JMeq_sym, eq_rect_r_JMeq with (F:=fun T => T).
  } Unfocus.
  intros.
  change f with (fieldlist_app Fnil f) in H0.
  cut (sigT (fun P => forall (v : reptype t) (v0 : nested_reptype_unionlist t gfs f)
       (v1 : reptype_unionlist f) (vs: reptype_unionlist (fieldlist_app Fnil f)),
     JMeq (proj_reptype t gfs v) vs ->
     reptype_suf_union vs v1 ->
     JMeq v0 v1 ->
     is_precise_proj_reptype_unionlist f id v1 = true ->
     nested_ufieldlist_at sh t gfs f v0 p =
     field_at sh t (id :: gfs) (proj_reptype t (id :: gfs) v) p * P)).
  Focus 1. {
    intro H2.
    destruct H2 as [P H3]; exists P.
    intros.
    destruct (reptype_suf_union_Fnil v1) as [x [? ?]].
    eapply H3 with (vs := x); eauto.
    rewrite H6.
    exact H2.
  } Unfocus.
  revert H0.
  generalize Fnil.
  induction f; intros.
  + inversion H1.
  + assert (fieldlist_no_replicate (fieldlist_app f0 (Fcons i0 t1 f)) = true).
    Focus 1. {
      pose proof nested_field_type2_nest_pred eq_refl _ gfs H.
      rewrite H0 in H2.
      simpl in H2.
      apply andb_true_iff in H2.
      tauto.
    } Unfocus.

    assert (reptype (nested_field_type2 t (i0 :: gfs)) = reptype t1)
      by (erewrite nested_field_type2_Tunion_mid; eauto).
    assert (nested_reptype_unionlist t gfs f = reptype_unionlist f).
    Focus 1. {
      unfold nested_field_type2 in H0.
      valid_nested_field_rec t gfs H0.
      subst t2.
      rewrite fieldlist_app_Fcons in H4.
      eapply eq_sym, nested_reptype_unionlist_lemma; eauto.
    } Unfocus.
    simpl in H1.
    if_tac in H1. (* whether id = the ident of head field *)
    - clear IHf. 
      simpl nested_ufieldlist_at.
Opaque field_at proj_reptype spacer nested_ufieldlist_at.
      destruct f; simpl;
      eexists; intros; [| destruct v0];
      try (rewrite withspacer_spacer; simpl).
Transparent field_at proj_reptype spacer nested_ufieldlist_at.
      * pose proof proj_reptype_cons_hd_Tunion_Fnil i f0 i0 t1 a0 t id gfs v vs v1 H H5 H0 H6 H7.
        subst.
        simpl in H10, H8.
        rewrite <- H10 in H8.
        apply JMeq_eq in H8.
        rewrite H8.
        rewrite sepcon_comm.
        match goal with
        | |- _ * ?T = _ => instantiate (1:= T)
        end.
        eauto.
      * rewrite sepcon_comm.
        f_equal.
        pose proof proj_reptype_cons_hd_Tunion_Fcons i f0 i0 t1 i1 t2 f a0 t id gfs v vs v1 H H5 H0 H6 H7.
        destruct v1.
        {
          apply JMeq_sumtype_ll in H8; auto.
          subst; f_equal.
          apply JMeq_eq.
          erewrite H10; eauto.
        } 
        {
          apply JMeq_sumtype_lr in H8; tauto.
        }
      * if_tac in H9; [| congruence].
        destruct v1; [apply JMeq_sumtype_rl in H8; tauto | inversion H9].
    - destruct f; try (solve [inversion H1]).
      rewrite fieldlist_app_Fcons in H0.
      destruct (IHf H1 (fieldlist_app f0 (Fcons i0 t1 Fnil)) H0) as [PH IH]; clear IHf.
(*      assert (forall (v0 : nested_reptype_unionlist t gfs (Fcons i0 t1 (Fcons i1 t2 f)))
       (v1 : reptype_unionlist (Fcons i0 t1 (Fcons i1 t2 f))),
        JMeq v0 v1 -> (JMeq (fst v0) (fst v1) /\ JMeq (snd v0) (snd v1))) by
        (intros; split; [apply JMeq_fst | apply JMeq_snd]; eauto).
*)      
Opaque field_at proj_reptype spacer nested_ufieldlist_at proj_except_reptype_unionlist.
      destruct (is_Fnil (all_fields_except_one2 (Fcons i1 t2 f) id)) eqn:HH; eexists; intros;
      replace (nested_ufieldlist_at sh t gfs (Fcons i0 t1 (Fcons i1 t2 f)) v0 p) with
        (match v0 with
        | inl v0' =>
            withspacer sh
              (nested_field_offset2 t (i0 :: gfs) +
               sizeof (nested_field_type2 t (i0 :: gfs)))
              (nested_field_offset2 t gfs + sizeof (nested_field_type2 t gfs))
              (field_at sh t (i0 :: gfs) v0') p
        | inr v0' =>
            nested_ufieldlist_at sh t gfs (Fcons i1 t2 f) v0' p
        end);
      simpl in H8; solve_JMeq_sumtype H8;
      try (rewrite withspacer_spacer; simpl).
Transparent field_at proj_reptype spacer nested_ufieldlist_at proj_except_reptype_unionlist.
      * simpl in H9; if_tac in H9; congruence.
      * destruct (reptype_suf_union_Fcons f0 i0 t1 i1 t2 f vs (inr r) H7) as [v2 [? HHH]].
        pose proof HHH r eq_refl; clear HHH.
        erewrite IH; eauto.
        {
          rewrite <- H10.
          exact H6.
        }
        {
          simpl in H9.
          if_tac in H9; [congruence |].
          exact H9.
        }
      * simpl in H9; if_tac in H9; congruence.
      * destruct (reptype_suf_union_Fcons f0 i0 t1 i1 t2 f vs (inr r) H7) as [v2 [? HHH]].
        pose proof HHH r eq_refl; clear HHH.
        erewrite IH; eauto.
        {
          rewrite <- H10.
          exact H6.
        }
        {
          simpl in H9.
          if_tac in H9; [congruence |].
          exact H9.
        }
Qed.
*)

Lemma proj_reptype_structlist_gupd_reptype_structlist_identical: forall f id t0 v v0,
  isSome (all_fields_replace_one f id t0) ->
  JMeq (proj_reptype_structlist id _ 0 (gupd_reptype_structlist f id t0 v v0)) v0.
Proof.
  intros.
  generalize 0; induction f; intros.
  + simpl in H.
    inversion H.
  + simpl in *.
    if_tac.
    - (* id = i *)
      simpl. revert v. if_tac.
      * intros; if_tac; [| congruence]. reflexivity.
      * intros; if_tac; [| congruence]. reflexivity.
    - (* id <> i *)
      destruct (is_Fnil f) eqn:?.
      * destruct f; [| inversion Heqb].
        simpl in H; inversion H.
      * simpl; if_tac; [congruence |].
        rewrite (is_Fnil_all_fields_replace_one2 f id t0), Heqb.
        simpl.
        apply IHf.
        destruct (all_fields_replace_one f id t0); [auto | inversion H].
Qed.

Lemma proj_reptype_unionlist_gupd_reptype_unionlist_identical: forall id t0 v0,
  JMeq (proj_reptype_unionlist id _ (gupd_reptype_unionlist id t0 v0)) v0.
Proof.
  intros.
  simpl.
  if_tac; [| congruence].
  reflexivity.
Qed.

Lemma proj_except_reptype_structlist_gupd_reptype_structlist: forall f id t0 v v0,
  JMeq (proj_except_reptype_structlist _ id (gupd_reptype_structlist f id t0 v v0)) (proj_except_reptype_structlist f id v).
Proof.
  intros.
  induction f.
  + simpl in *. destruct v. reflexivity.
  + simpl in *.
    if_tac.
    - (* id = i *)
      simpl. if_tac; [| congruence].
      destruct f; simpl; reflexivity.
    - (* id <> i *)
      simpl. if_tac; [congruence |].
      destruct (is_Fnil f) eqn:?.
      * destruct f; [| inversion Heqb].
        reflexivity.
      * rewrite (is_Fnil_all_fields_replace_one2 f id t0), Heqb.
        simpl.
        pattern (all_fields_except_one2 (all_fields_replace_one2 f id t0) id) at 1 3.
        rewrite (all_fields_except_one2_all_fields_replace_one2 id f t0).
        if_tac; [reflexivity |].
        generalize (IHf (snd v)).
        match goal with
        | |- JMeq ?M _ -> _ => generalize M
        end.
        rewrite (all_fields_except_one2_all_fields_replace_one2 id f t0).
        intros.
        rewrite H1.
        reflexivity.
Qed.

Lemma gupd_reptype_structlist_gupd_reptype_structlist: forall f id t0 t1 v v0 v1,
  JMeq (gupd_reptype_structlist _ id t1 (gupd_reptype_structlist f id t0 v v0) v1)
    (gupd_reptype_structlist f id t1 v v1).
Proof.
  intros.
  revert t0 t1 v0 v1.
  induction f; intros.
  + simpl. reflexivity.
  + simpl in *.
    if_tac.
    - (* id = i *)
      simpl; if_tac; [| congruence].
      simpl; if_tac; reflexivity.
    - (* id <> i *)
      simpl; if_tac; [congruence |].
      simpl.
      destruct (is_Fnil f) eqn:?.
      * simpl; rewrite !is_Fnil_all_fields_replace_one2, Heqb. reflexivity.
      * simpl; rewrite !is_Fnil_all_fields_replace_one2, Heqb.
        simpl. rewrite IHf.
        reflexivity.
Qed.

Lemma gupd_reptype_gupd_reptype: forall t gfs t0 t1 v v0 v1,
  isSome (nested_field_rec t gfs) ->
  JMeq (gupd_reptype (nf_replace2 t gfs t0) gfs t1 (gupd_reptype t gfs t0 v v0) v1) (gupd_reptype t gfs t1 v v1).
Proof.
  intros.
  revert t0 t1 v0 v1.
  induction gfs; intros.
  + simpl. reflexivity.
  + simpl; generalize (proj_reptype t gfs v).
    solve_nested_field_rec_cons_isSome H; rewrite H2; intros.
    - (* Tstruct *)
      generalize (proj_reptype_gupd_reptype t gfs v (Tstruct i (all_fields_replace_one2 f a t0) a0)
        (gupd_reptype_structlist f a t0 r v0) H0).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite nested_field_type2_nf_replace2; eauto; intros.
      rewrite H3.
      rewrite (IHgfs H0).
      generalize (gupd_reptype_structlist_gupd_reptype_structlist f a t0 t1 r v0 v1).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite all_fields_replace_one2_all_fields_replace_one2.
      intros.
      rewrite H4.
      reflexivity.
    - (* Tunion *)
      generalize (proj_reptype_gupd_reptype t gfs v (Tunion i (all_fields_replace_one2 f a t0) a0)
        (gupd_reptype_unionlist f a t0 v0) H0).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite nested_field_type2_nf_replace2; eauto; intros.
      rewrite (IHgfs H0).
      generalize (gupd_reptype_unionlist_gupd_reptype_unionlist f a t0 t1 v1).
      match goal with
      | |- JMeq ?M _ -> _ => generalize M
      end.
      rewrite all_fields_replace_one2_all_fields_replace_one2.
      intros.
      rewrite H4.
      reflexivity.
Qed.

Lemma proj_except_reptype_proj_except_reptype_cons_Tstruct: forall t id id0 gfs i f a t0 v,
  nested_field_type2 t (id0 :: gfs) = Tstruct i f a ->
  field_type id f = Errors.OK t0 ->
  JMeq (proj_except_reptype (nf_sub2 t id (id0 :: gfs)) id0 gfs (proj_except_reptype t id (id0 :: gfs) v)) (proj_except_reptype t id0 gfs v).
Proof.
  intros.
  apply JMeq_sym.
  unfold proj_except_reptype at 3.
  unfold nf_sub2.
  generalize (proj_reptype t (id0 :: gfs) v).
  rewrite H; intros.

  forget (proj_except_reptype_structlist f id r) as v0; clear r.
  clear t0 H0.
  revert v0.
  change (reptype_structlist (all_fields_except_one2 f id)) with (reptype (Tstruct i (all_fields_except_one2 f id) a)).
  forget (Tstruct i (all_fields_except_one2 f id) a) as t0.
  intros.

  assert (isSome (nested_field_rec t (id0 :: gfs)))
    by (eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto).
  simpl.
  generalize (proj_reptype t gfs v).
  solve_nested_field_rec_cons_isSome H0; rewrite H3; intros.
  + (* Tstruct *)
    generalize (proj_reptype_gupd_reptype t gfs v 
      (Tstruct i0 (all_fields_replace_one2 f0 id0 t0) a0) 
      (gupd_reptype_structlist f0 id0 t0 r v0) H1).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by apply H1.
    intros.
    rewrite gupd_reptype_gupd_reptype by auto.
    simpl in r0, H4.
    rewrite H4.
    generalize (proj_except_reptype_structlist_gupd_reptype_structlist f0 id0 t0 r v0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    intros.
    rewrite H5.
    reflexivity.
  + (* Tunion *)
    generalize (proj_reptype_gupd_reptype t gfs v 
      (Tunion i0 (all_fields_replace_one2 f0 id0 t0) a0) 
      (gupd_reptype_unionlist f0 id0 t0 v0) H1).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by apply H1.
    intros.
    rewrite gupd_reptype_gupd_reptype by auto.
    generalize (proj_except_reptype_unionlist_gupd_reptype_unionlist f0 id0 t0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    intros.
    rewrite H5.
    reflexivity.
Qed.

Lemma proj_except_reptype_proj_except_reptype_cons_Tstruct_eq_rect_r: forall t id id0 gfs i f a t0 v,
  nested_field_type2 t (id0 :: gfs) = Tstruct i f a ->
  field_type id f = Errors.OK t0 ->
  proj_except_reptype t id0 gfs v = eq_rect_r reptype 
   (proj_except_reptype _ id0 gfs (proj_except_reptype t id (id0 :: gfs) v))
   (eq_sym (nf_sub2_nf_sub2_cons _ _ _ _)).
Proof.
  intros.
  apply eq_sym, JMeq_eq.
  rewrite (eq_rect_r_JMeq type _ _ reptype (proj_except_reptype (nf_sub2 t id (id0 :: gfs)) id0 gfs
           (proj_except_reptype t id (id0 :: gfs) v)) (eq_sym (nf_sub2_nf_sub2_cons t id id0 gfs))).
  eapply proj_except_reptype_proj_except_reptype_cons_Tstruct; eauto.
Qed.

Lemma proj_reptype_proj_except_reptype_Tstruct: forall t id gfs i f a t0 v v1,
  nested_field_type2 t gfs = Tstruct i f a ->
  field_type id f = Errors.OK t0 ->
  JMeq (proj_reptype t gfs v) v1 ->
  JMeq (proj_reptype _ gfs (proj_except_reptype t id gfs v)) (proj_except_reptype_structlist f id v1).
Proof.
  intros.
  unfold proj_except_reptype, nf_sub2.
  revert H1; generalize (proj_reptype t gfs v). rewrite H.
  intros. rewrite H1.
  apply proj_reptype_gupd_reptype.
  eapply nested_field_type2_Tstruct_nested_field_rec_isSome; eauto.
Qed.

Lemma proj_reptype_proj_except_reptype_Tstruct_eq_rect_r: forall t id gfs i f a t0 v v1
  (H: nested_field_type2 t gfs = Tstruct i f a),
  field_type id f = Errors.OK t0 ->
  JMeq (proj_reptype t gfs v) v1 ->
  proj_except_reptype_structlist f id v1 = eq_rect_r reptype (proj_reptype _ gfs (proj_except_reptype t id gfs v)) (eq_sym (nested_field_type2_nf_sub2_Tstruct _ _ _ _ _ _ H)).
Proof.
  intros.
  apply eq_sym, JMeq_eq.
  pose proof (eq_rect_r_JMeq type _ _ reptype (proj_reptype (nf_sub2 t id gfs) gfs (proj_except_reptype t id gfs v)) (eq_sym (nested_field_type2_nf_sub2_Tstruct t id gfs i f a H))).
  simpl reptype in H2. rewrite H2.
  eapply proj_reptype_proj_except_reptype_Tstruct; eauto.
Qed.

Lemma proj_reptype_upd_reptype: forall t gfs v v0,
  isSome (nested_field_rec t gfs) ->
  proj_reptype t gfs (upd_reptype t gfs v v0) = v0.
Proof.
  intros.
  apply JMeq_eq.
  unfold upd_reptype.
  generalize (eq_rect_r_JMeq type _ _ reptype (gupd_reptype t gfs (nested_field_type2 t gfs) v v0)
    (nf_replace2_identical t gfs)).
  match goal with
  | |- JMeq ?M _ -> _ => generalize M
  end.
  pattern t at 1 2 7 8.
  rewrite (nf_replace2_identical t gfs).
  intros.
  rewrite H0.
  apply proj_reptype_gupd_reptype, H.
Qed.

Lemma proj_except_reptype_gupd_reptype_cons: forall t id gfs t0 v v0,
  isSome (nested_field_rec t (id :: gfs)) ->
  JMeq (proj_except_reptype _ id gfs (gupd_reptype t (id :: gfs) t0 v v0))
    (proj_except_reptype t id gfs v).
Proof.
  intros.
  unfold nf_sub2, proj_except_reptype.
  simpl gupd_reptype.
  simpl nf_replace2.
  generalize (proj_reptype t gfs v).
  solve_nested_field_rec_cons_isSome H; rewrite H2; intros.
  + (* Tstruct *)
    generalize (proj_reptype_gupd_reptype t gfs v (Tstruct i (all_fields_replace_one2 f id t0) a)
      (gupd_reptype_structlist f id t0 r v0) H0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by eauto.
    intros.
    rewrite H3.
    rewrite gupd_reptype_gupd_reptype by auto.
    generalize (proj_except_reptype_structlist_gupd_reptype_structlist f id _ r v0). 
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    intros.
    rewrite H4.
    reflexivity.
  + (* Tunion *)
    generalize (proj_reptype_gupd_reptype t gfs v (Tunion i (all_fields_replace_one2 f id t0) a)
      (gupd_reptype_unionlist f id t0 v0) H0).
    match goal with
    | |- JMeq ?M _ -> _ => generalize M
    end.
    erewrite nested_field_type2_nf_replace2 by eauto.
    intros.
    rewrite gupd_reptype_gupd_reptype by auto.
    unfold proj_except_reptype_unionlist.
    rewrite all_fields_except_one2_all_fields_replace_one2.
    reflexivity.
Qed.
    
Lemma proj_except_reptype_upd_reptype: forall t id gfs v v0,
  isSome (nested_field_rec t (id :: gfs)) ->
  proj_except_reptype t id gfs (upd_reptype t (id :: gfs) v v0) = proj_except_reptype t id gfs v.
Proof.
  intros.
  apply JMeq_eq.
  unfold upd_reptype.
  generalize (eq_rect_r_JMeq type _ _ reptype (gupd_reptype t (id :: gfs) (nested_field_type2 t (id :: gfs)) v v0) (nf_replace2_identical t (id :: gfs))).
  match goal with
  | |- JMeq ?M _ -> _ => generalize M
  end.
  pattern t at 1 2 7 8.
  rewrite (nf_replace2_identical t (id :: gfs)).
  intros.
  rewrite H0.
  apply proj_except_reptype_gupd_reptype_cons, H.
Qed.

Definition nested_field_sub_aux: forall sh t id gfs p, 
  nested_legal_fieldlist t = true ->
  legal_alignas_type t = true ->
  isSome (nested_field_rec t (id :: gfs)) ->
  sigT (fun P => forall v, data_at sh t v p = field_at sh t (id :: gfs) (proj_reptype t (id :: gfs) v) p * P (proj_except_reptype t id gfs v)).
Proof.
  intros.
  revert id H1.
  induction gfs; intros.
  + destruct t; try inversion H1.
    - (* Tstruct *)
Opaque proj_reptype.
      simpl.
Transparent proj_reptype.
      unfold nested_field_type in H1; simpl in H1.
      solve_field_offset_type id f; [clear H1 | inversion H1].
      destruct (nested_sfieldlist_at_sub sh (Tstruct i f a) id nil i f a p t H0 H eq_refl H3) as [P0 H1].
      exists P0; intros.
      rewrite data_at_field_at.
      pose proof H1 v v.
      simpl in H2. erewrite H2; eauto.
    - (* Tunion *)
Opaque proj_reptype.
      simpl.
Transparent proj_reptype.
      unfold nested_field_type in H1; simpl in H1.
      solve_field_offset_type id f; [clear H1 | inversion H1].
      admit.
  + remember (a:: gfs) as gfs0.
    solve_nested_field_rec_cons_isSome H1; subst gfs0.
    - (* Tstruct *)
      destruct (IHgfs a H2) as [PH IH]; clear IHgfs.
      destruct (field_type id f) eqn:?; [|inversion H3].
      destruct (nested_sfieldlist_at_sub sh t id (a :: gfs) i f a0 p t0 H0 H H4 Heqr) as [P0 H5].

      eexists; intros; rewrite IH.

      pose (eq_rect_r reptype (proj_reptype t (a :: gfs) v) (eq_sym H4)) as v1.
      assert (JMeq (proj_reptype t (a :: gfs) v) v1).
        subst v1.
        eapply JMeq_sym, eq_rect_r_JMeq.
      simpl reptype in v1, H6.
      erewrite H5; eauto.
      erewrite proj_except_reptype_proj_except_reptype_cons_Tstruct_eq_rect_r; eauto.
      erewrite proj_reptype_proj_except_reptype_Tstruct_eq_rect_r with (H := H4); eauto.
      rewrite sepcon_assoc.
      f_equal.
      instantiate (1 := fun v' => P0 (eq_rect_r reptype
        (proj_reptype (nf_sub2 t id (a :: gfs)) (a :: gfs) v')
        (eq_sym (nested_field_type2_nf_sub2_Tstruct t id (a :: gfs) i f a0 H4))) *
        PH (eq_rect_r reptype
        (proj_except_reptype (nf_sub2 t id (a :: gfs)) a gfs v')
        (eq_sym (nf_sub2_nf_sub2_cons t id a gfs)))).
Opaque eq_rect_r proj_reptype proj_except_reptype.
      simpl.
      reflexivity.
Transparent eq_rect_r proj_reptype proj_except_reptype.
    - (* Tunion *)
      admit.
Defined.
*)

Lemma semax_extract_later_prop': 
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (PP : Prop) P Q R c post,
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- !!PP ->
      (PP -> semax Delta (|>PROPx P (LOCALx Q (SEPx R))) c post) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) c post.
Proof.
  intros.
  eapply semax_pre_simple.
  + hoist_later_left.
    rewrite insert_local.
    apply later_derives.
    rewrite (add_andp _ _ H).
    rewrite <- insert_local.
    rewrite andp_assoc.
    apply andp_left2.
    rewrite andp_comm.
    apply derives_refl.
  + apply semax_extract_later_prop.
    auto.
Qed.

Lemma corable_efield_denote: forall efs gfs rho, corable (efield_denote efs gfs rho).
Proof.
  intros.
  revert gfs; induction efs; destruct gfs; simpl; intros.
  + apply corable_prop.
  + apply corable_prop.
  + destruct a; apply corable_prop.
  + destruct a, g; try apply corable_prop.
    - unfold local, lift1.
      unfold_lift.
      repeat apply corable_andp.
      apply corable_prop.
      apply corable_prop.
      apply IHefs.
    - apply corable_andp.
      apply corable_prop.
      apply IHefs.
    - apply corable_andp.
      apply corable_prop.
      apply IHefs.
Qed.

Lemma insert_corable_sep: forall R1 P Q R,
  (forall rho, corable (R1 rho)) ->
  R1 && PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx (R1 && emp :: R))).
Proof.
  intros.
  rewrite andp_comm.
  unfold PROPx.
  rewrite andp_assoc; f_equal.
  unfold LOCALx.
  rewrite andp_assoc; f_equal.
  unfold SEPx.
  extensionality rho.
  simpl.
  rewrite andp_comm.
  rewrite andp_left_corable by auto.
  reflexivity.
Qed.

(************************************************

Lemmas of field nested load/store

************************************************)

Lemma nested_efield_app: forall t gfs0 gfs1 tts0 tts1,
  length gfs1 = length tts1 ->
  nested_efield (nested_efield t gfs0 tts0) gfs1 tts1 = 
    nested_efield t (gfs1 ++ gfs0) (tts1 ++ tts0).
Proof.
  intros.
  revert tts1 H.
  induction gfs1; intros; destruct tts1; try solve [inversion H].
  + reflexivity.
  + inversion H.
    simpl.
    rewrite (IHgfs1 tts1 H1).
    reflexivity.
Qed.

(*
Lemma legal_nested_efield_app: forall env t_root e gfs0 gfs1 tts0 tts1,
  length gfs1 = length tts1 ->
  legal_nested_efield env t_root e (gfs1 ++ gfs0) (tts1 ++ tts0) = true ->
  legal_nested_efield env t_root e gfs0 tts0 = true.
Proof.
  intros.
  revert tts1 H H0.
  induction gfs1; intros; destruct tts1; try solve [inversion H].
  + auto.
  + inversion H.
    simpl in H0.
    match type of H0 with
    |  (match ?M with | Some _ => _ | _ => _ end = true) => destruct M as [[? ?]|]; [|inversion H0]
    end.
    apply andb_true_iff in H0.
    destruct H0.
    eapply IHgfs1; eauto.
Qed.

Lemma efield_denote_app: forall Delta efs1 efs0 gfs1 gfs0,
  length efs1 = length gfs1 ->
  efield_denote Delta (efs1 ++ efs0) (gfs1 ++ gfs0) |-- efield_denote Delta efs0 gfs0.
Proof.
  intros.
  revert efs1 H.
  induction gfs1; intros; destruct efs1; try solve [inversion H].
  + auto.
  + inversion H.
    simpl efield_denote.
    intros rho.
    destruct e, a; try (change (!! False) with FF; apply FF_left);
    apply andp_left2; apply IHgfs1; auto.
Qed.
*)

(*
Lemma legal_nested_efield_app': forall e t gfs0 gfs1 tts0 tts1,
  length gfs1 = length tts1 ->
  legal_nested_efield e t (gfs1 ++ gfs0) (tts1 ++ tts0) = true ->
  legal_nested_efield e (uncompomize e (nested_field_type2 t gfs0)) gfs1 tts1 = true.
Proof.
Opaque uncompomize nested_field_rec.
  intros.
  revert tts1 H H0.
  induction gfs1; intros; destruct tts1; try solve [inversion H].
  + simpl in *. rewrite uncompomize_uncompomize. apply eqb_type_refl.
  + simpl in *.
    rewrite nested_field_rec_uncompomize_cons.
    valid_nested_field_rec t (a :: gfs1 ++ gfs0) H0.
    rewrite andb_true_iff in H0.
    assert (isSome (nested_field_rec t ((a :: gfs1) ++ gfs0))) by (simpl; rewrite H1; simpl; auto).
    pose proof nested_field_rec_app_isSome _ _ _ H2.
    pose proof nested_field_rec_app_isSome' _ _ _ H2.
    valid_nested_field_rec (nested_field_type2 t gfs0) (a :: gfs1) H4.
    destruct H0.
    rewrite IHgfs1 by auto.
    unfold nested_field_type2 in H5.
    valid_nested_field_rec t gfs0 H3.
    pose proof nested_field_rec_app _ _ _ _ _ _ _ H7 H5.
    simpl in H8.
    rewrite H1 in H8.
    inversion H8.
    subst.
    rewrite H6.
    reflexivity.
Transparent uncompomize nested_field_rec. 
Qed.

Lemma efield_denote_app': forall Delta efs1 efs0 gfs1 gfs0,
  length efs1 = length gfs1 ->
  efield_denote Delta (efs1 ++ efs0) (gfs1 ++ gfs0) |--
    efield_denote Delta efs1 gfs1.
Proof.
  intros.
  revert efs1 H.
  induction gfs1; intros; destruct efs1; try solve [inversion H].
  + apply prop_right, I.
  + inversion H.
    simpl efield_denote.
    intros rho.
    destruct e, a; try (change (!! False) with FF; apply FF_left);
    (apply andp_derives; [apply derives_refl |]);
    apply IHgfs1; auto.
Qed.
*)

(*
Lemma lifted_field_except_at_lemma: forall sh t gf gfs0 gfs1 v v0 v0',
  legal_nested_field t ((gf :: gfs1) ++ gfs0) ->
  JMeq v0' v0 ->
  `(field_at sh t gfs0)
     (`(upd_reptype (nested_field_type2 t gfs0) (gf :: gfs1)) v v0) =
       `(field_at sh t (gf :: gfs1 ++ gfs0)) v0' *
       (`(field_except_at sh t gf gfs0 gfs1)
         (`(proj_except_reptype (nested_field_type2 t gfs0) gf gfs1) v)).
Proof.
  intros.
  extensionality p rho.
  unfold_lift.
Opaque upd_reptype.
  simpl.
Transparent upd_reptype.
  erewrite field_except_at_lemma with (v0' := v0' rho); eauto.
  clear - H0.
  revert v0 v0' H0.
  rewrite nested_field_type2_nested_field_type2.
  intros.
  rewrite H0.
  reflexivity.
Qed.
*)

Lemma semax_nested_efield_field_load_37':
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      repinject _ (proj_reptype (nested_field_type t_root gfs0) gfs1 v') = v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
         (tc_LR Delta e1 lr) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
         (tc_efield Delta efs) &&
        efield_denote efs gfs &&
        (`(field_at sh t_root gfs0 v') (eval_LR e1 lr) * TT) ->
      legal_nested_field t_root gfs ->
      readable_share sh ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
Admitted.
(*
  intros.
  destruct gfs1 as [| gf gfs1]; (simpl in H1; subst gfs).
  + eapply semax_max_path_field_load_37'; eauto.
  + destruct efs as [| ef efs].
    Focus 1. {
      simpl efield_denote in H4.
      apply semax_extract_later_prop' with (PP := False); [| intros; tauto].
      eapply derives_trans; [exact H4 |].
      normalize.
    } Unfocus.
    destruct tts as [| ttt tts].
    Focus 1. {
      simpl legal_nested_efield in H2.
      inversion H2.
    } Unfocus.
    apply semax_extract_later_prop' with
      (uncompomize e (nested_field_type2 t_root ((gf :: gfs1) ++ gfs0)) =
        typeof (nested_efield e1 (ef :: efs) (ttt :: tts))).
    Focus 1. {
      eapply derives_trans; [exact H4 |].
      rewrite (andp_comm _ (_ * _)).
      rewrite !andp_assoc.
      rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ _ lr H2)).
      solve_andp_left.
    } Unfocus.
    pose proof I as H1.
    intros.
    assert (type_is_by_value (uncompomize e (nested_field_type2 t_root ((gf :: gfs1) ++ gfs0))) = true)
      by (rewrite H6; eapply is_neutral_cast_by_value, H0).
    eapply semax_max_path_field_load_37' with (v'0 := valinject _ v); eauto.
    - erewrite repinject_valinject; [reflexivity |].
      exact H7.
    - eapply derives_trans; [exact H4 |].
      apply andp_derives; [apply derives_refl |].
      simpl; intro rho; unfold_lift.
      eapply derives_trans; [
        apply sepcon_derives; [
           | apply derives_refl]
        |].
      Focus 1. {
        apply field_at_stronger.
        apply stronger_upd_self with (gfs := (gf :: gfs1)).
        apply legal_nested_field_app'; auto.
      } Unfocus.
      erewrite field_except_at_lemma; eauto.
      * simpl; rewrite sepcon_assoc.
        eapply sepcon_derives; [apply derives_refl | apply prop_right, I].
      * subst.
        change (gf :: gfs1 ++ gfs0) with ((gf :: gfs1) ++ gfs0).
        rewrite <- nested_field_type2_nested_field_type2.
        erewrite valinject_repinject; [reflexivity |].
        rewrite nested_field_type2_nested_field_type2.
        exact H7.
Qed.
*)
Lemma semax_nested_efield_field_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh id P Q R (e1: expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (v : val) (v' : reptype (nested_field_type t_root gfs0)) lr,
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 efs tts)) = true ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      repinject _ (proj_reptype (nested_field_type t_root gfs0) gfs1 v') = v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
         (tc_LR Delta e1 lr) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 efs tts)) t v))) &&
         (tc_efield Delta efs) &&
        efield_denote efs gfs &&
        (`(field_at sh t_root gfs0 v') (eval_LR e1 lr) * TT) ->
      legal_nested_field t_root gfs ->
      readable_share sh ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 efs tts) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (`(eq (eval_cast (typeof (nested_efield e1 efs tts)) t v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Admitted.
(*
Proof.
  intros.
  destruct gfs1 as [| gf gfs1]; (simpl in H1; subst gfs).
  + eapply semax_max_path_field_cast_load_37'; eauto.
  + destruct efs as [| ef efs].
    Focus 1. {
      simpl efield_denote in H4.
      apply semax_extract_later_prop' with (PP := False); [| intros; tauto].
      eapply derives_trans; [exact H4 |].
      normalize.
    } Unfocus.
    destruct tts as [| ttt tts].
    Focus 1. {
      simpl legal_nested_efield in H2.
      inversion H2.
    } Unfocus.
    apply semax_extract_later_prop' with
      (uncompomize e (nested_field_type2 t_root ((gf :: gfs1) ++ gfs0)) =
        typeof (nested_efield e1 (ef :: efs) (ttt :: tts))).
    Focus 1. {
      eapply derives_trans; [exact H4 |].
      rewrite (andp_comm _ (_ * _)).
      rewrite !andp_assoc.
      rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ _ lr H2)).
      solve_andp_left.
    } Unfocus.
    pose proof I as H1.
    intros.
    assert (type_is_by_value (uncompomize e (nested_field_type2 t_root ((gf :: gfs1) ++ gfs0))) = true) by (rewrite H6; apply H0).
    eapply semax_max_path_field_cast_load_37' with (v'0 := valinject _ v); eauto.
    - erewrite repinject_valinject; [reflexivity |].
      exact H7.
    - eapply derives_trans; [exact H4 |].
      apply andp_derives; [apply derives_refl |].
      simpl; intro rho; unfold_lift.
      eapply derives_trans; [
        apply sepcon_derives; [
           | apply derives_refl]
        |].
      Focus 1. {
        apply field_at_stronger.
        apply stronger_upd_self with (gfs := (gf :: gfs1)).
        apply legal_nested_field_app'; auto.
      } Unfocus.
      erewrite field_except_at_lemma; eauto.
      * simpl; rewrite sepcon_assoc.
        eapply sepcon_derives; [apply derives_refl | apply prop_right, I].
      * subst.
        change (gf :: gfs1 ++ gfs0) with ((gf :: gfs1) ++ gfs0).
        rewrite <- nested_field_type2_nested_field_type2.
        erewrite valinject_repinject; [reflexivity |].
        rewrite nested_field_type2_nested_field_type2.
        exact H7.
Qed.
*)
Lemma semax_nested_efield_field_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh n P Q R Rn (e1 e2 : expr)
      (t t_root: type) (efs: list efield) (gfs0 gfs1 gfs: list gfield) (tts: list type)
      (v: environ -> reptype (nested_field_type t_root gfs0)) lr,
      typeof (nested_efield e1 efs tts) = t ->
      type_is_by_value t = true ->
      gfs = gfs1 ++ gfs0 ->
      legal_nested_efield t_root e1 gfs tts lr = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at sh t_root gfs0) v (eval_LR e1 lr) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
         (tc_LR Delta e1 lr) && 
         (tc_efield Delta efs) &&
        efield_denote efs gfs &&
         (tc_expr Delta (Ecast e2 t)) ->
      legal_nested_field t_root gfs ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh t_root gfs0)
                      (`(upd_reptype (nested_field_type t_root gfs0) gfs1) v
                        (`(valinject (nested_field_type (nested_field_type t_root gfs0) gfs1)) (eval_expr (Ecast e2 t))))
                          (eval_LR e1 lr)
                            )))))).
Admitted.
(*
Proof.
  intros.
  destruct gfs1 as [| gf gfs1]; (simpl in H1; subst gfs).
  + simpl app in *.
    change (`(upd_reptype (nested_field_type2 t_root gfs0) nil) v
      (`(valinject _) (eval_expr (Ecast e2 t)))) with
      (`(valinject (nested_field_type2 t_root gfs0)) (eval_expr (Ecast e2 t))).
    eapply semax_max_path_field_store_nth; eauto.
    eapply derives_trans; [exact H4 |].
    unfold_lift; simpl; intros.
    apply field_at_field_at_.
  + destruct efs as [| ef efs].
    Focus 1. {
      simpl efield_denote in H6.
      apply semax_extract_later_prop' with (PP := False); [| intros; tauto].
      eapply derives_trans; [exact H6 |].
      normalize.
    } Unfocus.
    destruct tts as [| ttt tts].
    Focus 1. {
      simpl legal_nested_efield in H2.
      inversion H2.
    } Unfocus.
    apply semax_extract_later_prop' with
      (uncompomize e (nested_field_type2 t_root ((gf :: gfs1) ++ gfs0)) =
        typeof (nested_efield e1 (ef :: efs) (ttt :: tts))).
    Focus 1. {
      eapply derives_trans; [exact H6 |].
      rewrite (andp_comm _ (local (tc_expr _ _))).
      rewrite !andp_assoc.
      rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ _ lr H2)).
      solve_andp_left.
    } Unfocus.
    pose proof I as H1.
    intros.
    assert (forall rho : environ, corable
      ((local (tc_LR Delta e1 lr) && local (tc_expr Delta (Ecast e2 t)) &&
        local (tc_efield Delta (ef :: efs)) &&
        efield_denote (ef :: efs) ((gf :: gfs1) ++ gfs0)) rho)).
    Focus 1. {
      intros.
      unfold local, lift1.
Opaque efield_denote.
      simpl.
Transparent efield_denote.
      apply corable_andp; [apply corable_andp; [apply corable_andp |] |].
            (* I dont know why this line takes pretty long time. Though it works. *)
      apply corable_prop.
      apply corable_prop.
      apply corable_prop.
      apply corable_efield_denote.
    } Unfocus.
    apply semax_pre_simple with (P' := |> PROPx P (LOCALx Q (SEPx 
      (local (tc_LR Delta e1 lr) && local (tc_expr Delta (Ecast e2 t)) &&
       local (tc_efield Delta (ef :: efs)) &&
       efield_denote (ef :: efs) ((gf :: gfs1) ++ gfs0) && emp :: R)))).
    Focus 1. {
      hoist_later_left.
      apply later_derives.
      rewrite insert_local.
      rewrite (add_andp _ _ H6).
      rewrite <- insert_corable_sep by exact H9.
      rewrite (andp_comm _ (PROPx P (LOCALx Q (SEPx R)))).
      rewrite <- insert_local.
      repeat apply andp_right; solve_andp_left.
    } Unfocus.
    assert (PROPx P (LOCALx (tc_environ Delta :: Q) SEP  (Rn))
       |-- `(field_at sh t_root gfs0)
             (`(upd_reptype _ (gf :: gfs1)) v (`(proj_reptype _ (gf :: gfs1)) v))
               (eval_LR e1 lr)).
    Focus 1. {
      eapply derives_trans; [exact H4 |].
      intro rho.
      unfold_lift.
      apply field_at_stronger; auto.
      apply stronger_upd_self; auto.
      apply legal_nested_field_app'; auto.
    } Unfocus.
    clear H4.
    assert (nth_error (local (tc_LR Delta e1 lr) &&
                 local (tc_expr Delta (Ecast e2 t)) &&
                 local (tc_efield Delta (ef :: efs)) &&
                 efield_denote (ef :: efs) ((gf :: gfs1) ++ gfs0) &&
                 emp :: R) (1 + n) = Some Rn)
      by (exact H3).
    clear H3.
    assert (type_is_by_value (uncompomize e (nested_field_type2 t_root ((gf :: gfs1) ++ gfs0))) = true).
    Focus 1. {
      rewrite H8, H.
      exact H0.
    } Unfocus.
    erewrite lifted_field_except_at_lemma
      with (v0' := `(valinject _) (`(repinject _) (`(proj_reptype (nested_field_type2 t_root gfs0)
                      (gf :: gfs1)) v))) in H10; eauto.
    Focus 2. { admit. } Unfocus. (* JMeq about valinject and repinject *)
    match goal with
    | |- appcontext [replace_nth n R ?M] =>
         replace M with
           (`(field_at sh t_root ((gf :: gfs1) ++ gfs0)) (`(valinject _) (eval_expr (Ecast e2 t)))
              (eval_LR e1 lr) *
            `(field_except_at sh t_root gf gfs0 gfs1)
               (`(proj_except_reptype (nested_field_type2 t_root gfs0) gf
                    gfs1) v) (eval_LR e1 lr))
    end.
    Focus 2. {
      unfold_lift.
      extensionality rho.
Opaque upd_reptype.
      simpl.
Transparent upd_reptype.
      erewrite field_except_at_lemma; simpl; eauto.
      admit. (* JMeq about valinject and repinject *)
    } Unfocus.
    rewrite (replace_nth_nth_error _ _ _ H4) by exact H3.
    eapply semax_pre_simple.
    {
      hoist_later_left.
      apply later_derives.
      rewrite insert_local.
      apply replace_nth_SEP'.
      eapply derives_trans; [| exact H10].
      simpl; intro; normalize.
    }
    erewrite !SEP_replace_nth_isolate; eauto.
    match goal with
    | |- appcontext [SEPx ((?A * ?B) ?p :: replace_nth (1 + n) (?C :: R) emp)] =>
           replace (SEPx ((A * B) p :: replace_nth (1 + n) (C :: R) emp)) with
             (SEPx (C :: A p :: B p :: replace_nth n R emp))
    end.
    Focus 2. {
      extensionality.
      unfold SEPx.
Opaque efield_denote.
      simpl.
Transparent efield_denote.
      rewrite <- !sepcon_assoc.
      apply pred_ext; cancel.
    } Unfocus.
    match goal with
    | |- appcontext [SEPx (?A * ?B :: replace_nth n R emp)] =>
      match goal with
      | |- appcontext [SEPx (_ :: ?C :: _ :: replace_nth n R emp)] =>
           replace (SEPx (A * B :: replace_nth n R emp)) with
             (SEPx (replace_nth 0%nat (C :: B :: replace_nth n R emp) A))
      end
    end.
    Focus 2. {
      simpl (replace_nth 0%nat).
      extensionality.
      unfold SEPx.
      simpl.
      rewrite <- sepcon_assoc.
      reflexivity.
    } Unfocus.
    eapply semax_post'; 
      [ |eapply semax_max_path_field_store_nth with (n0 := 1%nat) 
       (Rn0 := `(field_at sh t_root ((gf :: gfs1) ++ gfs0))
              (`(valinject (nested_field_type2 t_root ((gf :: gfs1) ++ gfs0)))
                 (`(repinject
                      (nested_field_type2 (nested_field_type2 t_root gfs0)
                         (gf :: gfs1)))
                    (`(proj_reptype (nested_field_type2 t_root gfs0)
                         (gf :: gfs1)) v))) (eval_LR e1 lr)); eauto].
    - unfold replace_nth at 1 3.
      rewrite <- insert_corable_sep by exact H9.
      rewrite <- insert_local.
      apply andp_left2.
      apply andp_left2.
      apply derives_refl.
    - simpl; intros; normalize.
      apply field_at_field_at_; auto.
    - rewrite <- insert_corable_sep by exact H9.
      apply andp_left1.
      (repeat apply andp_right); solve_andp_left.
Qed.
*)
Arguments eq_rect_r /.

End DATA_AT_WITH_HOLES.