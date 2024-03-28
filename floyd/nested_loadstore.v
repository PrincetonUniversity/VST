Require Import VST.floyd.base2.

Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.loadstore_field_at.
(* Import DataCmpNotations. *)
Import LiftNotation.

Section NESTED_RAMIF.

Context `{!VSTGS OK_ty Σ} {cs: compspecs}.

Lemma reptype_Tarray_JMeq_constr0: forall t gfs t0 n a (v: reptype (nested_field_type t gfs)),
  legal_nested_field t gfs ->
  nested_field_type t gfs = Tarray t0 n a ->
  {v': list (reptype (nested_field_type t (ArraySubsc 0 :: gfs))) |
   JMeq v v'}.
Proof.
  intros.
  apply JMeq_sigT.
  rewrite ->@nested_field_type_ind with (gfs := cons _ _).
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
  rewrite ->@nested_field_type_ind with (gfs := cons _ _).
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
  rewrite ->@nested_field_type_ArraySubsc with (i := i).
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

Lemma data_at_type_changeable:
  forall {cs : compspecs} (sh : Share.t) (t1 t2 : type) 
    (v1 : reptype t1) (v2 : reptype t2),
  t1 = t2 -> JMeq v1 v2 -> data_at sh t1 v1 = data_at sh t2 v2.
Proof.
 intros.
 subst.
  f_equal.
  apply JMeq_eq in H0. auto.
Qed.

Lemma field_at_type_changeable:
  forall {cs : compspecs} (sh : Share.t) (t1 t2 : type) 
  (EQt: t1=t2)
  (g1 g2: list gfield)
  (EQg: g1 = g2)
  v1 v2,
  JMeq v1 v2 -> field_at sh t1 g1 v1 = field_at sh t2 g2 v2.
Proof.
 intros.
 subst.
  f_equal.
  apply JMeq_eq in H. auto.
Qed.

Ltac rewrite_field_at_type_changeable :=
  match goal with | |- field_at ?sh ?t1 ?g1 ?v1 = field_at ?sh ?t2 ?g2 ?v2 =>
  rewrite (field_at_type_changeable sh t1 t2 _ g1 g2 _ v1 v2) // end.

Lemma JMeq_field_type_name_member {CS: compspecs} i m :
  forall a, JMeq (@field_type_name_member CS i m a) a.
Proof.
intros.
unfold field_type_name_member.
unfold eq_rect.
destruct (name_member_get i m ).
apply JMeq_refl.
Qed.

(* This lemma is mainly dealing with all JMeq subtle issues and combine 3 ramif lemmas together. *)
Lemma gfield_ramif: forall sh t gfs gf v v0 p,
  JMeq (proj_gfield_reptype (nested_field_type t gfs) gf v) v0 ->
  field_compatible t (gf :: gfs) p ->
  field_at sh t gfs v p ⊢ field_at sh t (gf :: gfs) v0 p ∗
    (∀ v0': _,
      (field_at sh t (gf :: gfs) v0' p -∗
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
    erewrite field_at_Tarray; [| eauto | eauto | lia | eauto].
    assert(Hrrt:
      (∀ v0' : _,
        field_at sh t (gfs SUB i) v0' p -∗
        field_at sh t gfs
          (upd_gfield_reptype (nested_field_type t gfs)
             (ArraySubsc i) v
             (eq_rect_r reptype v0'
                (eq_sym (nested_field_type_ind t (gfs SUB i))))) p)
      ⊣⊢
      (∀ v0' : _, (∀  v0'': _,
        ⌜JMeq v0' v0''⌝ →
        (field_at sh t (gfs SUB i) v0' p -∗
         array_at sh t gfs 0 z (upd_Znth (i - 0) v' v0'') p)))).
    {
      rewrite Z.sub_0_r.
      clear v0 H.
      apply bi.equiv_entails_2.
      + apply bi.forall_mono; intro v0.
        apply bi.forall_intro => v0'.
        apply bi.impl_intro_l; normalize.
        apply bi.wand_mono; auto.
        destruct (reptype_Tarray_JMeq_constr1 t gfs t0 z a i v0) as [v0'' ?H]; auto.
        erewrite field_at_Tarray; [apply derives_refl | eauto | eauto | lia |].
        clear v0'' H5.
        set (v0'' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gfs SUB i)))).
        assert (JMeq v0' v0'') by (apply JMeq_sym; eapply JMeq_trans; [apply eq_rect_r_JMeq | auto]).
        clearbody v0''; clear v0 H.
        revert v v0'' H4 H5; rewrite H2; intros.
        unfold upd_gfield_reptype.
        eapply JMeq_trans; [apply fold_reptype_JMeq |].
        apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
        revert v' v0' H4 H5; rewrite ->@nested_field_type_ind with (gfs := cons _ _), H2; simpl; intros.
        apply JMeq_eq in H4; apply JMeq_eq in H5.
        subst; apply JMeq_refl.
      + apply bi.forall_intro; intro v0.
        rewrite (bi.forall_elim v0).
        destruct (reptype_Tarray_JMeq_constr2 t gfs t0 z a i v0) as [v0' ?H]; auto.
        rewrite (bi.forall_elim v0').
        rewrite ->prop_imp by auto.
        apply bi.wand_mono; auto.
        erewrite field_at_Tarray; [apply derives_refl | eauto | eauto | lia |].
        set (v0'' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gfs SUB i)))).
        assert (JMeq v0' v0'') by (apply JMeq_sym; eapply JMeq_trans; [apply eq_rect_r_JMeq | auto]).
        clearbody v0''; clear v0 H.
        revert v v0'' H4 H5; rewrite H2; intros.
        unfold upd_gfield_reptype.
        eapply JMeq_trans; [apply fold_reptype_JMeq |].
        apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
        revert v' v0' H4 H5; rewrite ->@nested_field_type_ind with (gfs := cons _ _), H2; simpl; intros.
        apply JMeq_eq in H4; apply JMeq_eq in H5.
        subst; apply JMeq_refl.
    }
    rewrite Hrrt; clear Hrrt.
    apply (array_at_ramif sh t gfs t0 z a 0 z i v' v0 p); auto.
    eapply JMeq_trans; [apply @JMeq_sym, H |]; clear v0 H.
    revert v v' H4.
    rewrite ->@nested_field_type_ind with (gfs := cons _ _), H2.
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
    etrans; [eapply nested_sfieldlist_at_ramif; eauto |].
    apply bi.sep_mono.
    - apply entails_refl'.
      apply equal_f.
      rewrite_field_at_type_changeable.
      rewrite name_member_get; auto.
      eapply JMeq_trans; [| exact H].
      clear v0 H.
      revert v H4; rewrite H2; intros.
      unfold proj_gfield_reptype.
      apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
      forget (unfold_reptype v) as v''; clear v.
      cbv iota beta in v''.
      unfold reptype_structlist in v''.
      unfold nested_reptype_structlist in v'.
      match goal with |- context [field_type_name_member ?A] =>
           apply (@JMeq_trans _ _ _ _ A); [ | apply JMeq_sym, JMeq_field_type_name_member]
     end.
     * apply (@proj_compact_prod_JMeq _ (get_member i (co_members (get_co i0)))
             _
             (fun it : member => @reptype cs (@nested_field_type cs t (@cons gfield (StructField (name_member it)) gfs)))
             (fun it => reptype (field_type (name_member it) (co_members (get_co i0))))); auto.
      -- intros.
        rewrite nested_field_type_ind H2; reflexivity.
      -- apply in_get_member; auto.
    - clear v0 H.
set (i' := name_member (get_member i (co_members (get_co i0)))).
trans
 (∀ v0' : reptype (nested_field_type t (gfs DOT i')),
    field_at sh t (gfs DOT i') v0' p -∗
    field_at sh t gfs
      (upd_gfield_reptype (nested_field_type t gfs) 
         (StructField i') v
         (eq_rect_r reptype v0' (eq_sym (nested_field_type_ind t (gfs DOT i')))))
      p).
    *
      apply bi.forall_mono; intro v0.
      apply bi.wand_mono; auto.
      erewrite field_at_Tstruct; [apply derives_refl | eauto |].
      set (v0' := eq_rect_r reptype v0 (eq_sym (nested_field_type_ind t (gfs DOT i')))).
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
      unfold upd_struct.
      apply upd_compact_prod_JMeq; auto.
      unfold i'. rewrite name_member_get; auto.
      intros.
      rewrite nested_field_type_ind H2.
      reflexivity.
      eapply JMeq_trans. 
      apply eq_rect_r_JMeq; auto. auto.
     * apply bi.forall_intro. intro v0.
       rewrite bi.forall_elim.
       instantiate (1:=@eq_rect_r _ i (fun i => reptype (nested_field_type t (gfs DOT i))) v0 i'
                          (name_member_get _ _)).
       apply bi.wand_mono.
       apply entails_refl'. apply equal_f.
       rewrite_field_at_type_changeable.
       f_equal. f_equal. symmetry; apply name_member_get.
       subst i'. clear.
       rewrite -> name_member_get. unfold eq_rect_r. simpl. apply JMeq_refl.
       apply entails_refl'. apply equal_f.
       rewrite_field_at_type_changeable.
       subst i'. clear. rewrite -> name_member_get.
       apply JMeq_refl.
  + pose proof H0.
    rewrite field_compatible_cons in H1.
    (* A Coq bug here. I cannot do destruct eqn in H1. So using next two lines instead. *)
    remember (nested_field_type t gfs) as t0 eqn:H2 in H1.
    destruct t0; try tauto; symmetry in H2.
    destruct H1.
    destruct (reptype_Tunion_JMeq_constr0 t gfs i0 a v) as [v' ?H]; auto.
    erewrite field_at_Tunion by eauto.
    etrans; [eapply nested_ufieldlist_at_ramif; eauto |].
    apply bi.sep_mono.
    - apply entails_refl'.
      apply equal_f.
      rewrite_field_at_type_changeable.
      rewrite name_member_get; auto.
      eapply JMeq_trans; [| exact H].
      clear v0 H.
      revert v H4; rewrite H2; intros.
      unfold proj_gfield_reptype.
      apply (JMeq_trans (unfold_reptype_JMeq _ v)) in H4.
      forget (unfold_reptype v) as v''; clear v.
      cbv iota beta in v''.
      unfold reptype_structlist in v''.
      unfold nested_reptype_unionlist in v'.
      eapply JMeq_trans; [ | apply JMeq_sym; apply JMeq_field_type_name_member].
      apply (@proj_compact_sum_JMeq' _ (get_member i (co_members (get_co i0)))
             _
             (fun it => reptype (nested_field_type t (gfs UDOT name_member it)))
             (fun it => reptype (field_type (name_member it) (co_members (get_co i0))))); auto.
      * intros.
        rewrite nested_field_type_ind H2; reflexivity.
      * rewrite nested_field_type_ind H2; apply JMeq_refl.
    - clear v0 H.
      set (i' := name_member _).
      apply bi.forall_intro  ; intro v0.
      rewrite (bi.forall_elim (eq_rect i (fun i => reptype (nested_field_type t (gfs UDOT i))) v0 i'
                                       (eq_sym (name_member_get _ _)))).
       apply bi.wand_mono. 
       * apply entails_refl'.
         apply equal_f.
         rewrite_field_at_type_changeable.
         subst i'; rewrite name_member_get; auto.
         apply JMeq_sym.
         subst i'; clear.
         rewrite -> name_member_get; auto.
      *
      subst i'.
      set (u := upd_union _ _ _ _).
      rewrite ->@field_at_Tunion with (id:=i0) (a:=a)(v2:=u); auto.
      subst u.
      set (v0' := eq_rect_r _ _ _).
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
      rewrite nested_field_type_ind H2.
      reflexivity.
      fold (eq_rect_r (fun i1 : ident => reptype (nested_field_type t (gfs UDOT i1))) v0
           (name_member_get i (co_members (get_co i0)))).
      clear v'' H4.
      clear v'.
      clear - H.
      eapply JMeq_trans. apply eq_rect_r_JMeq.
      eapply JMeq_trans; [ apply H |]. clear v0' H.
      unfold eq_rect_r. rewrite -> name_member_get. apply JMeq_refl.
Qed.

Lemma nested_field_ramif: forall sh t gfs0 gfs1 v v0 p,
  JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v) v0 ->
  field_compatible t (gfs1 ++ gfs0) p ->
  field_at sh t gfs0 v p ⊢
    field_at sh t (gfs1 ++ gfs0) v0 p ∗
    (∀ v0': _, ∀ v0'': _, ⌜ JMeq v0' v0''⌝ →
      (field_at sh t (gfs1 ++ gfs0) v0' p -∗
         field_at sh t gfs0 (upd_reptype (nested_field_type t gfs0) gfs1 v v0'') p)).
Proof.
  intros.
  rewrite allp_uncurry.
  revert v0 H; induction gfs1 as [| gf gfs1]; intros.
  + simpl in *.
    rewrite /eq_rect_r /= in H.
    apply JMeq_eq in H as <-.
    iIntros "$" (??) "?".
    rewrite /eq_rect_r /=.
    apply JMeq_eq in H as <-; done.
  + simpl app in H0, v0, H |- *.
    assert ({v1: reptype (nested_field_type t (gfs1 ++ gfs0)) | JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v) v1} ) as (v1 & ?H)
      by (apply JMeq_sigT; rewrite nested_field_type_nested_field_type; auto).
    rewrite IHgfs1 //; clear IHgfs1.
    2: { rewrite field_compatible_cons in H0. destruct (nested_field_type t (gfs1 ++ gfs0)), gf; tauto. }
    rewrite gfield_ramif //.
    2: { instantiate (1 := v0).
         eapply JMeq_trans; [| apply H].
         clear - H1.
         unfold proj_reptype; fold proj_reptype.
         eapply JMeq_trans; [| apply @JMeq_sym, eq_rect_r_JMeq].
         revert v1 H1; rewrite <- nested_field_type_nested_field_type; intros.
         apply JMeq_eq in H1; subst v1.
         apply JMeq_refl. }
    iIntros "(($ & H1) & H2)" ((va, vb) Heq) "?"; simpl fst in *; simpl snd in *.
    iSpecialize ("H1" with "[$]").
    unfold upd_reptype; fold upd_reptype.
    set (v0'' := eq_rect_r reptype va (eq_sym (nested_field_type_ind t (gf :: gfs1 ++ gfs0)))).
    set (v0''' := eq_rect_r reptype vb (eq_sym (nested_field_type_ind (nested_field_type t gfs0) (gf :: gfs1)))).
    assert (JMeq v0'' v0''') by (eapply JMeq_trans; [apply eq_rect_r_JMeq | apply (JMeq_trans Heq), @JMeq_sym, eq_rect_r_JMeq]).
    clearbody v0'' v0'''.
    clear v0 H va vb Heq.
    iApply ("H2" $! (upd_gfield_reptype (nested_field_type t (gfs1 ++ gfs0)) gf v1 v0'',
      upd_gfield_reptype (nested_field_type (nested_field_type t gfs0) gfs1) gf
        (proj_reptype (nested_field_type t gfs0) gfs1 v) v0''') with "[%] [$]"); simpl.
    revert v0'' v1 H0 H1 H2.
    change (gf :: gfs1 ++ gfs0) with ((gf :: gfs1) ++ gfs0).
    rewrite -nested_field_type_nested_field_type.
    intros.
    apply JMeq_eq in H1; subst v1.
    apply JMeq_eq in H2; subst v0'''.
    done.
Qed.

(* use <absorb>? *)
Lemma nested_field_ramif_load: forall sh t gfs0 gfs1 (v_reptype: reptype (nested_field_type t gfs0)) (v_val: val) p,
  field_compatible t (gfs1 ++ gfs0) p ->
  JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v_reptype) v_val ->
  exists v_reptype',
    JMeq v_reptype' v_val /\
    (field_at sh t gfs0 v_reptype p ⊢
      field_at sh t (gfs1 ++ gfs0) v_reptype' p ∗ True).
Proof.
  intros.
  generalize (JMeq_refl (proj_reptype (nested_field_type t gfs0) gfs1 v_reptype)).
  set (v0 := proj_reptype (nested_field_type t gfs0) gfs1 v_reptype) at 2.
  clearbody v0.
  revert v0.
  pattern (reptype (nested_field_type (nested_field_type t gfs0) gfs1)) at 1 3.
  rewrite {2}nested_field_type_nested_field_type.
  intros; exists v0.
  split.
  1: eapply JMeq_trans; [apply @JMeq_sym |]; eassumption.
  etrans; [apply nested_field_ramif; eassumption |].
  apply bi.sep_mono; auto.
Qed.

Lemma nested_field_ramif_store: forall sh t gfs0 gfs1 (v_reptype: reptype (nested_field_type t gfs0)) (v0_reptype: reptype (nested_field_type (nested_field_type t gfs0) gfs1)) (v_val: val) p,
  field_compatible t (gfs1 ++ gfs0) p ->
  JMeq v0_reptype v_val ->
  exists v0_reptype',
    JMeq v0_reptype' v_val /\
    (field_at sh t gfs0 v_reptype p ⊢
      field_at_ sh t (gfs1 ++ gfs0) p ∗
       (field_at sh t (gfs1 ++ gfs0) v0_reptype' p -∗
          field_at sh t gfs0 (upd_reptype (nested_field_type t gfs0) gfs1 v_reptype v0_reptype) p)).
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
  rewrite {3}nested_field_type_nested_field_type.
  intros; exists v0_reptype'.
  split.
  1: eapply JMeq_trans; [apply @JMeq_sym |]; eassumption.
  etrans; [apply nested_field_ramif; eassumption |].
  apply bi.sep_mono.
  1: apply field_at_field_at_.
  iIntros "H"; iApply "H"; auto.
Qed.

Lemma nested_field_ramif': forall sh t gfs0 gfs1 v v0 p,
  JMeq (proj_reptype (nested_field_type t gfs0) gfs1 v) v0 ->
  legal_nested_field t (gfs1 ++ gfs0) ->
  field_at sh t gfs0 v p ⊢
    field_at sh t (gfs1 ++ gfs0) v0 p ∗
    (∀ v0': _, ∀ v0'': _, ⌜JMeq v0' v0''⌝ →
      (field_at sh t (gfs1 ++ gfs0) v0' p -∗
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
  field_at sh t gfs0 v p ⊢
    field_at sh t (gfs1 ++ gfs0) v0 p ∗
    (∀ v0': _, ∀ v0'': _, ⌜JMeq v0' v0''⌝ →
      (field_at sh t (gfs1 ++ gfs0) v0' p -∗
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

Lemma semax_extract_later_prop' :
  forall `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {cs: compspecs} ,
    forall E (Delta : tycontext) (PP : Prop) P Q R c post,
      ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) ⊢ ⌜PP⌝ ->
      (PP -> semax E Delta (▷PROPx P (LOCALx Q (SEPx R))) c post) ->
      semax E Delta (▷PROPx P (LOCALx Q (SEPx R))) c post.
Proof.
  intros.
  eapply semax_pre_simple.
  + hoist_later_left.
    apply bi.later_mono.
    rewrite (add_andp _ _ H).
    rewrite -bi.and_assoc.
    apply bi.and_elim_r.
  + rewrite bi.and_comm. apply semax_extract_later_prop1.
    auto.
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

Lemma field_at_app `{!VSTGS OK_ty Σ} {cs: compspecs}:
 forall sh t gfs1 gfs2 v v' p,
 JMeq v v' ->
 field_at sh t (gfs1++gfs2) v p ⊣⊢
 field_at sh (nested_field_type t gfs2) gfs1 v' (field_address t gfs2 p).
Proof.
intros.
rewrite !field_at_data_at.
rewrite (data_at_type_changeable sh
   (nested_field_type t (gfs1 ++ gfs2))
  (nested_field_type (nested_field_type t gfs2) gfs1) v v'); auto.
f_equiv.
apply field_address_app.
symmetry; apply nested_field_type_nested_field_type.
Qed.
