Require Import VST.floyd.base2.

Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.stronger.
Require Import VST.floyd.entailer.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.loadstore_field_at.
Import DataCmpNotations.

Local Open Scope logic.

Section NESTED_RAMIF.

Context {cs: compspecs}.

Lemma reptype_Tarray_JMeq_constr0: forall t gfs t0 n a (v: reptype (nested_field_type t gfs)),
  legal_nested_field t gfs ->
  nested_field_type t gfs = Tarray t0 n a ->
  {v': list (reptype (nested_field_type t (ArraySubsc 0 :: gfs))) |
   JMeq v v'}.
Proof.
  intros.
  apply JMeq_sigT.
  rewrite nested_field_type_ind with (gfs0 := cons _ _).
  rewrite !H0.
  rewrite reptype_eq.
  auto.
Qed.

Lemma reptype_Tarray_JMeq_constr1: forall t gfs t0 n a i (v: reptype (nested_field_type t (ArraySubsc i :: gfs))),
  legal_nested_field t gfs ->
  nested_field_type t gfs = Tarray t0 n a ->
  {v': reptype (gfield_type (nested_field_type t gfs) (ArraySubsc i)) |
   JMeq v v'}.
Proof.
  intros.
  apply JMeq_sigT.
  rewrite nested_field_type_ind with (gfs0 := cons _ _).
  reflexivity.
Qed.

Lemma reptype_Tarray_JMeq_constr2: forall t gfs t0 n a i (v': reptype (nested_field_type t (ArraySubsc i :: gfs))),
  legal_nested_field t gfs ->
  nested_field_type t gfs = Tarray t0 n a ->
  {v: reptype (nested_field_type t (ArraySubsc 0 :: gfs)) |
   JMeq v' v}.
Proof.
  intros.
  apply JMeq_sigT.
  rewrite nested_field_type_ArraySubsc with (i0 := i).
  auto.
Qed.

Lemma reptype_Tstruct_JMeq_constr0: forall t gfs id a (v: reptype (nested_field_type t gfs)),
  legal_nested_field t gfs ->
  nested_field_type t gfs = Tstruct id a ->
  {v' : nested_reptype_structlist t gfs (co_members (get_co id)) |
   JMeq v v'}.
Proof.
  intros.
  apply JMeq_sigT.
  eapply nested_reptype_structlist_lemma; eauto.
Qed.

Lemma reptype_Tunion_JMeq_constr0: forall t gfs id a (v: reptype (nested_field_type t gfs)),
  legal_nested_field t gfs ->
  nested_field_type t gfs = Tunion id a ->
  {v' : nested_reptype_unionlist t gfs (co_members (get_co id)) |
   JMeq v v'}.
Proof.
  intros.
  apply JMeq_sigT.
  eapply nested_reptype_unionlist_lemma; eauto.
Qed.

(* This lemma is mainly dealing with all JMeq subtle issues and combine 3 ramif lemmas together. *)
Lemma gfield_ramif: forall sh t gfs gf v v0 p,
  JMeq (proj_gfield_reptype (nested_field_type t gfs) gf v) v0 ->
  field_compatible t (gf :: gfs) p ->
  field_at sh t gfs v p |-- field_at sh t (gf :: gfs) v0 p *
    (ALL v0': _,
      (field_at sh t (gf :: gfs) v0' p -*
         field_at sh t gfs
           (upd_gfield_reptype (nested_field_type t gfs) gf v
              (eq_rect_r reptype v0' (eq_sym (nested_field_type_ind t _))))
           p)).
Proof.
  intros.
  destruct gf.
  + (* ArraySubsc *)
    pose proof H0.
    rewrite field_compatible_cons in H1.
    (* A Coq bug here. I cannot do destruct eqn in H1. So using next two lines instead. *)
    remember (nested_field_type t gfs) as t0 eqn:H2 in H1.
    destruct t0; try tauto; symmetry in H2.
    destruct H1.
    destruct (reptype_Tarray_JMeq_constr0 t gfs t0 z a v) as [v' ?H]; auto.
    erewrite field_at_Tarray; [| eauto | eauto | omega | eauto].
    replace
      (ALL  v0' : _,
        field_at sh t (gfs SUB i) v0' p -*
        field_at sh t gfs
          (upd_gfield_reptype (nested_field_type t gfs)
             (ArraySubsc i) v
             (eq_rect_r reptype v0'
                (eq_sym (nested_field_type_ind t (gfs SUB i))))) p)
    with
      (ALL  v0' : _, (ALL  v0'': _,
        !!JMeq v0' v0'' -->
        (field_at sh t (gfs SUB i) v0' p -*
         array_at sh t gfs 0 z (upd_Znth (i - 0) v' v0'') p))).
    2:{
      rewrite Z.sub_0_r.
      clear v0 H.
      apply pred_ext.
      + apply allp_right; intro v0.
        apply (allp_left _ v0).
        destruct (reptype_Tarray_JMeq_constr2 t gfs t0 z a i v0) as [v0' ?H]; auto.
        apply (allp_left _ v0').
        rewrite prop_imp by auto.
        apply wand_derives; auto.
        erewrite field_at_Tarray; [apply derives_refl | eauto | eauto | omega |].
        set (v0'' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gfs SUB i)))).
        assert (JMeq v0' v0'') by (apply JMeq_sym; eapply JMeq_trans; [apply eq_rect_r_JMeq | auto]).
        clearbody v0''; clear v0 H.
        revert v v0'' H4 H5; rewrite H2; intros.
        unfold upd_gfield_reptype.
        eapply JMeq_trans; [apply fold_reptype_JMeq |].
        apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
        revert v' v0' H4 H5; rewrite nested_field_type_ind with (gfs0 := cons _ _), H2; simpl; intros.
        apply JMeq_eq in H4; apply JMeq_eq in H5.
        subst; apply JMeq_refl.
      + apply allp_right; intro v0.
        apply allp_right; intro v0'.
        apply (allp_left _ v0).
        apply imp_andp_adjoint; normalize.
        apply wand_derives; auto.
        destruct (reptype_Tarray_JMeq_constr1 t gfs t0 z a i v0) as [v0'' ?H]; auto.
        erewrite field_at_Tarray; [apply derives_refl | eauto | eauto | omega |].
        clear v0'' H5.
        set (v0'' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gfs SUB i)))).
        assert (JMeq v0' v0'') by (apply JMeq_sym; eapply JMeq_trans; [apply eq_rect_r_JMeq | auto]).
        clearbody v0''; clear v0 H.
        revert v v0'' H4 H5; rewrite H2; intros.
        unfold upd_gfield_reptype.
        eapply JMeq_trans; [apply fold_reptype_JMeq |].
        apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
        revert v' v0' H4 H5; rewrite nested_field_type_ind with (gfs0 := cons _ _), H2; simpl; intros.
        apply JMeq_eq in H4; apply JMeq_eq in H5.
        subst; apply JMeq_refl.
    }
    apply (array_at_ramif sh t gfs t0 z a 0 z i v' v0 p); auto.
    eapply JMeq_trans; [apply @JMeq_sym, H |]; clear v0 H.
    revert v v' H4.
    rewrite nested_field_type_ind with (gfs0 := cons _ _), H2.
    unfold proj_gfield_reptype, gfield_type.
    intros.
    apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
    apply JMeq_eq in H4; subst.
    rewrite Z.sub_0_r.
    subst; apply JMeq_refl.
  + pose proof H0.
    rewrite field_compatible_cons in H1.
    (* A Coq bug here. I cannot do destruct eqn in H1. So using next two lines instead. *)
    remember (nested_field_type t gfs) as t0 eqn:H2 in H1.
    destruct t0; try tauto; symmetry in H2.
    destruct H1.
    destruct (reptype_Tstruct_JMeq_constr0 t gfs i0 a v) as [v' ?H]; auto.
    erewrite field_at_Tstruct by eauto.
    eapply derives_trans; [eapply nested_sfieldlist_at_ramif; eauto |].
    apply sepcon_derives.
    - apply derives_refl'.
      f_equal.
      apply JMeq_eq.
      eapply JMeq_trans; [| exact H].
      clear v0 H.
      revert v H4; rewrite H2; intros.
      unfold proj_gfield_reptype.
      apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
      forget (unfold_reptype v) as v''; clear v.
      cbv iota beta in v''.
      unfold reptype_structlist in v''.
      unfold nested_reptype_structlist in v'.
      apply (@proj_compact_prod_JMeq _ (i, field_type i (co_members (get_co i0)))
             _
             (fun it : prod ident type => @reptype cs (@nested_field_type cs t (@cons gfield (StructField (@fst ident type it)) gfs)))
             (fun it => reptype (field_type (fst it) (co_members (get_co i0))))); auto.
      * intros.
        rewrite nested_field_type_ind, H2; reflexivity.
      * apply in_members_field_type; auto.
    - clear v0 H.
      apply allp_derives; intro v0.
      apply wand_derives; auto.
      erewrite field_at_Tstruct; [apply derives_refl | eauto |].
      set (v0' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gfs DOT i)))).
      assert (JMeq v0' v0) by apply eq_rect_r_JMeq.
      clearbody v0'.
      revert v v0' H H4.
      rewrite H2.
      unfold gfield_type, upd_gfield_reptype.
      intros.
      apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
      forget (unfold_reptype v) as v''; clear v.
      cbv iota beta in v''.
      eapply JMeq_trans; [apply fold_reptype_JMeq |].
      apply upd_compact_prod_JMeq; auto.
      intros.
      rewrite nested_field_type_ind, H2.
      reflexivity.
  + pose proof H0.
    rewrite field_compatible_cons in H1.
    (* A Coq bug here. I cannot do destruct eqn in H1. So using next two lines instead. *)
    remember (nested_field_type t gfs) as t0 eqn:H2 in H1.
    destruct t0; try tauto; symmetry in H2.
    destruct H1.
    destruct (reptype_Tunion_JMeq_constr0 t gfs i0 a v) as [v' ?H]; auto.
    erewrite field_at_Tunion by eauto.
    eapply derives_trans; [eapply nested_ufieldlist_at_ramif; eauto |].
    apply sepcon_derives.
    - apply derives_refl'.
      f_equal.
      apply JMeq_eq.
      eapply JMeq_trans; [| exact H].
      clear v0 H.
      revert v H4; rewrite H2; intros.
      unfold proj_gfield_reptype.
      apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
      forget (unfold_reptype v) as v''; clear v.
      cbv iota beta in v''.
      unfold reptype_structlist in v''.
      unfold nested_reptype_unionlist in v'.
      apply (@proj_compact_sum_JMeq' _ (i, field_type i (co_members (get_co i0)))
             _
             (fun it => reptype (nested_field_type t (gfs UDOT fst it)))
             (fun it => reptype (field_type (fst it) (co_members (get_co i0))))); auto.
      * intros.
        rewrite nested_field_type_ind, H2; reflexivity.
      * rewrite nested_field_type_ind, H2; apply JMeq_refl.
    - clear v0 H.
      apply allp_derives; intro v0.
      apply wand_derives; auto.
      erewrite field_at_Tunion; [apply derives_refl | eauto |].
      set (v0' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gfs UDOT i)))).
      assert (JMeq v0' v0) by apply eq_rect_r_JMeq.
      clearbody v0'.
      revert v v0' H H4.
      rewrite H2.
      unfold gfield_type, upd_gfield_reptype.
      intros.
      apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
      forget (unfold_reptype v) as v''; clear v.
      cbv iota beta in v''.
      eapply JMeq_trans; [apply fold_reptype_JMeq |].
      apply upd_compact_sum_JMeq; auto.
      intros.
      rewrite nested_field_type_ind, H2.
      reflexivity.
Qed.

Lemma nested_field_ramif: forall sh t gfs0 gfs1 v v0 p,
  JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v) v0 ->
  field_compatible t (gfs1 ++ gfs0) p ->
  field_at sh t gfs0 v p |--
    field_at sh t (gfs1 ++ gfs0) v0 p *
    (ALL v0': _, ALL v0'': _, !! JMeq v0' v0'' -->
      (field_at sh t (gfs1 ++ gfs0) v0' p -*
         field_at sh t gfs0 (upd_reptype (nested_field_type t gfs0) gfs1 v v0'') p)).
Proof.
  intros.
  rewrite allp_uncurry'.
  RAMIF_Q'.formalize.
  revert v0 H; induction gfs1 as [| gf gfs1]; intros.
  + simpl app in *.
    apply RAMIF_Q'.solve with emp.
    - simpl; auto.
    - simpl in H. unfold eq_rect_r in H; rewrite <- eq_rect_eq in H; apply JMeq_eq in H.
      rewrite H, sepcon_emp; auto.
    - clear v0 H.
      intros [v0 v0']; unfold fst, snd.
      normalize.
      simpl.
      unfold eq_rect_r; rewrite <- eq_rect_eq; apply JMeq_eq in H.
      rewrite H; auto.
  + simpl app in H0, v0, H |- *.
    assert ({v1: reptype (nested_field_type t (gfs1 ++ gfs0)) | JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v) v1})
      by (apply JMeq_sigT; rewrite nested_field_type_nested_field_type; auto).
    destruct X as [v1 ?H].
    change
      (fun st: reptype (nested_field_type t (gf :: gfs1 ++ gfs0)) *
               reptype (nested_field_type (nested_field_type t gfs0) (gf :: gfs1)) =>
       field_at sh t (gf :: gfs1 ++ gfs0) (fst st) p)
    with
      (Basics.compose
        (fun v => field_at sh t (gf :: gfs1 ++ gfs0) v p)
        (fun st: reptype (nested_field_type t (gf :: gfs1 ++ gfs0)) *
               reptype (nested_field_type (nested_field_type t gfs0) (gf :: gfs1)) =>
         fst st)).
    change (fun st: reptype (nested_field_type t (gf :: gfs1 ++ gfs0)) *
               reptype (nested_field_type (nested_field_type t gfs0) (gf :: gfs1)) =>
       field_at sh t gfs0
         (upd_reptype (nested_field_type t gfs0) (gf :: gfs1) v (snd st)) p)
      with
      (Basics.compose
        (fun st: reptype (nested_field_type t (gfs1 ++ gfs0)) *
                 reptype (nested_field_type (nested_field_type t gfs0) gfs1) =>
         field_at sh t gfs0
           (upd_reptype (nested_field_type t gfs0) gfs1 v (snd st)) p)
        (fun st: reptype (nested_field_type t (gf :: gfs1 ++ gfs0)) *
                 reptype (nested_field_type (nested_field_type t gfs0) (gf :: gfs1)) =>
           (upd_gfield_reptype _ gf v1 (eq_rect_r reptype (fst st) (eq_sym (nested_field_type_ind _ (gf :: _)))),
            upd_gfield_reptype _ gf (proj_reptype _ gfs1 v) (eq_rect_r reptype (snd st) (eq_sym (nested_field_type_ind _ (gf :: _))))))).
    eapply RAMIF_Q'.trans with
      (pL := fun _ => !! True)
      (pG := fun st => !! JMeq (fst st) (snd st)).
    - simpl; auto.
    - simpl; auto.
    - simpl; auto.
    - apply IHgfs1; clear IHgfs1.
      * clear - H0.
        rewrite field_compatible_cons in H0.
        destruct (nested_field_type t (gfs1 ++ gfs0)), gf; tauto.
      * exact H1.
    - eapply derives_trans; [apply gfield_ramif |].
      * instantiate (1 := v0).
        eapply JMeq_trans; [| apply H].
        clear - H1.
        unfold proj_reptype; fold proj_reptype.
        eapply JMeq_trans; [| apply @JMeq_sym, eq_rect_r_JMeq].
        revert v1 H1; rewrite <- nested_field_type_nested_field_type; intros.
        apply JMeq_eq in H1; subst v1.
        apply JMeq_refl.
      * auto.
      * apply sepcon_derives; auto.
        apply allp_derives; intros v0'.
        Opaque nested_field_type_ind. simpl. Transparent nested_field_type_ind.
        rewrite prop_imp by auto.
        apply derives_refl.
    - intros; apply prop_right; auto.
    - clear v0 H.
      intros [v0 v0']; unfold fst, snd.
      apply andp_derives; [| auto].
      apply prop_derives; intro.
      clear - H H1.
      set (v0'' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gf :: gfs1 ++ gfs0)))).
      set (v0''' := eq_rect_r reptype v0' (eq_sym (nested_field_type_ind (nested_field_type t gfs0) (gf :: gfs1)))).
      assert (JMeq v0'' v0''') by (eapply JMeq_trans; [apply eq_rect_r_JMeq | apply (JMeq_trans H), @JMeq_sym, eq_rect_r_JMeq]).
      clearbody v0'' v0'''.
      clear v0 v0' H.
      revert v0'' v1 H0 H1.
      change (gf :: gfs1 ++ gfs0) with ((gf :: gfs1) ++ gfs0).
      rewrite <- nested_field_type_nested_field_type.
      intros.
      apply JMeq_eq in H1; subst v1.
      apply JMeq_eq in H0; subst v0'''.
      apply JMeq_refl.
Qed.

Lemma nested_field_ramif_load: forall sh t gfs0 gfs1 (v_reptype: reptype (nested_field_type t gfs0)) (v_val: val) p,
  field_compatible t (gfs1 ++ gfs0) p ->
  JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v_reptype) v_val ->
  exists v_reptype',
    JMeq v_reptype' v_val /\
    field_at sh t gfs0 v_reptype p |--
      field_at sh t (gfs1 ++ gfs0) v_reptype' p * TT.
Proof.
  intros.
  generalize (JMeq_refl (proj_reptype (nested_field_type t gfs0) gfs1 v_reptype)).
  set (v0 := proj_reptype (nested_field_type t gfs0) gfs1 v_reptype) at 2.
  clearbody v0.
  revert v0.
  pattern (reptype (nested_field_type (nested_field_type t gfs0) gfs1)) at 1 3.
  rewrite nested_field_type_nested_field_type at 1.
  intros; exists v0.
  split.
  1: eapply JMeq_trans; [apply @JMeq_sym |]; eassumption.
  eapply derives_trans; [apply nested_field_ramif; eassumption |].
  apply sepcon_derives; auto.
Qed.

Lemma nested_field_ramif_store: forall sh t gfs0 gfs1 (v_reptype: reptype (nested_field_type t gfs0)) (v0_reptype: reptype (nested_field_type (nested_field_type t gfs0) gfs1)) (v_val: val) p,
  field_compatible t (gfs1 ++ gfs0) p ->
  JMeq v0_reptype v_val ->
  exists v0_reptype',
    JMeq v0_reptype' v_val /\
    field_at sh t gfs0 v_reptype p |--
      field_at_ sh t (gfs1 ++ gfs0) p *
       (field_at sh t (gfs1 ++ gfs0) v0_reptype' p -*
          field_at sh t gfs0 (upd_reptype (nested_field_type t gfs0) gfs1 v_reptype v0_reptype) p).
Proof.
  intros.
  generalize (JMeq_refl (proj_reptype (nested_field_type t gfs0) gfs1 v_reptype)).
  set (v0 := proj_reptype (nested_field_type t gfs0) gfs1 v_reptype) at 2.
  clearbody v0.
  generalize (JMeq_refl v0_reptype).
  set (v0_reptype' := v0_reptype) at 2.
  clearbody v0_reptype'.
  revert v0 v0_reptype'.
  pattern (reptype (nested_field_type (nested_field_type t gfs0) gfs1)) at 1 2 4 6.
  rewrite nested_field_type_nested_field_type at 1.
  intros; exists v0_reptype'.
  split.
  1: eapply JMeq_trans; [apply @JMeq_sym |]; eassumption.
  eapply derives_trans; [apply nested_field_ramif; eassumption |].
  apply sepcon_derives.
  1: apply field_at_field_at_.
  eapply allp_left.
  eapply allp_left.
  rewrite prop_imp; [apply derives_refl |].
  auto.
Qed.

Lemma nested_field_ramif': forall sh t gfs0 gfs1 v v0 p,
  JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v) v0 ->
  legal_nested_field t (gfs1 ++ gfs0) ->
  field_at sh t gfs0 v p |--
    field_at sh t (gfs1 ++ gfs0) v0 p *
    (ALL v0': _, ALL v0'': _, !! JMeq v0' v0'' -->
      (field_at sh t (gfs1 ++ gfs0) v0' p -*
         field_at sh t gfs0 (upd_reptype (nested_field_type t gfs0) gfs1 v v0'') p)).
Proof.
  intros.
  rewrite field_at_compatible'.
  normalize.
  eapply nested_field_ramif; eauto.
  unfold field_compatible in *.
  tauto.
Qed.

Lemma nested_field_ramif'': forall sh t gfs0 gfs1 v v0 p,
  JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v) v0 ->
  legal_nested_field (nested_field_type t gfs0) gfs1 ->
  field_at sh t gfs0 v p |--
    field_at sh t (gfs1 ++ gfs0) v0 p *
    (ALL v0': _, ALL v0'': _, !! JMeq v0' v0'' -->
      (field_at sh t (gfs1 ++ gfs0) v0' p -*
         field_at sh t gfs0 (upd_reptype (nested_field_type t gfs0) gfs1 v v0'') p)).
Proof.
  intros.
  rewrite field_at_compatible'.
  normalize.
  eapply nested_field_ramif; eauto.
  pose proof legal_nested_field_app_inv t gfs0 gfs1.
  unfold field_compatible in *.
  tauto.
Qed.

End NESTED_RAMIF.

Lemma semax_extract_later_prop' {cs: compspecs}:
  forall {Espec: OracleKind},
    forall (Delta : tycontext) (PP : Prop) P Q R c post,
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- !!PP ->
      (PP -> semax Delta (|>PROPx P (LOCALx Q (SEPx R))) c post) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) c post.
Proof.
  intros.
  eapply semax_pre_simple.
  + hoist_later_left.
    apply later_derives.
    rewrite (add_andp _ _ H).
    rewrite andp_assoc.
    apply andp_left2.
    rewrite andp_comm.
    apply derives_refl.
  + apply semax_extract_later_prop1.
    auto.
Qed.

Lemma insert_corable_sep: forall R1 P Q R,
  corable R1 ->
  `R1 && PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx Q (SEPx (R1 && emp :: R))).
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
