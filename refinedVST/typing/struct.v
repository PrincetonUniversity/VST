From iris.algebra Require Import list.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs bytes.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.
Require Import Coq.Program.Equality.

Section struct.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* Should the struct type be indexed by a name or a composite (CompCert's analogue of struct_layout)? A name, because
     that's where has_layout_loc is defined (on Ctypes.type). *)

  (* We state the sidecondition using foldr instead of Forall since this is faster to solve for the automation. *)
  Definition is_struct_ot (i : ident) (tys : list type) (ot : Ctypes.type) (mt : memcast_compat_type) : Prop :=
    match (cenv_cs !! i)%maps, ot with
    | Some sl, Tstruct i' _ => sl.(co_su) = Struct ∧ length (sl.(co_members)) = length tys ∧
        i' = i ∧ mt ≠ MCId ∧
        foldr (λ x, and (x.1.(ty_has_op_type) (field_type (name_member x.2) sl.(co_members)) mt)) True%type (zip tys sl.(co_members))
    | _, _ => False
    end.

  Lemma is_struct_ot_layout i tys ot mt:
    is_struct_ot i tys ot mt → ∃ a, ot = Tstruct i a.
  Proof. rewrite /is_struct_ot. destruct (cenv_cs !! i)%maps, ot; naive_solver. Qed.

  Lemma is_struct_ot_forall i tys ot mt:
    is_struct_ot i tys ot mt →
    (∃ a, ot = Tstruct i a) /\ ∃ sl, (cenv_cs !! i)%maps = Some sl /\
    Forall2 (λ m ty, exists mt, ty.(ty_has_op_type) (field_type (name_member m) sl.(co_members)) mt) sl.(co_members) tys.
  Proof.
    rewrite /is_struct_ot. destruct (cenv_cs !! i)%maps, ot; try done.
    intros (? & ? & -> & ? & H); split; first eauto.
    eexists; split; first done.
    rewrite -Forall_fold_right in H.
    apply: Forall2_same_length_lookup_2 => //.
    intros j ?? Hc Ht; eapply (Forall_lookup_1 _ _ j (_, _)) in H; simpl in *; eauto.
    rewrite lookup_zip_with Ht /= Hc //.
  Qed.

  Lemma has_layout_struct_noattr : forall i a l, l `has_layout_loc` (Tstruct i a) ↔ l `has_layout_loc` (Tstruct i noattr).
  Proof.
    intros; rewrite /has_layout_loc /field_compatible; do 3 f_equiv; last f_equiv; try done.
    rewrite /align_compatible_dec.align_compatible /=.
    split; inversion 1; try done; eapply align_compatible_rec_Tstruct; done.
  Qed.

  Import EqNotations.

  Lemma mapsto_struct : forall id a l v, l ↦|Tstruct id a| v ⊣⊢ aggregate_pred.struct_pred (co_members (get_co id))
    (fun it v => mapsto_memory_block.withspacer Tsh (field_offset cenv_cs (name_member it) (co_members (get_co id)) + sizeof (field_type (name_member it) (co_members (get_co id))))
                        (field_offset_next cenv_cs (name_member it) (co_members (get_co id)) (co_sizeof (get_co id)))
                        (mapsto_memory_block.at_offset (data_at_rec Tsh (field_type (name_member it) (co_members (get_co id))) v) (field_offset cenv_cs (name_member it) (co_members (get_co id)))))
    (unfold_reptype v) l.
  Proof.
    intros; rewrite /mapsto data_at_rec_eq //.
  Qed.

  (* up *)
  Lemma struct_pred_fupd : forall E m {A} (P : forall it, A it -> val -> mpred) v p,
    aggregate_pred.struct_pred m (λ it a v, |={E}=> P it a v) v p ⊢ |={E}=> aggregate_pred.struct_pred m P v p.
  Proof.
    induction m; intros.
    - simpl; by iIntros.
    - destruct m; first done.
      setoid_rewrite struct_pred_cons2.
      setoid_rewrite IHm.
      apply fupd_sep.
  Qed.

  Global Instance struct_pred_persistent : forall m {A} (P : forall it, A it -> val -> mpred) v p,
    (forall it a v, Persistent (P it a v)) -> Persistent (aggregate_pred.struct_pred m P v p).
  Proof.
    induction m; intros.
    - simpl. apply _.
    - destruct m; first apply _.
      setoid_rewrite struct_pred_cons2.
      apply bi.sep_persistent; apply _.
  Qed.

  Definition make_ty_prod (tys : list type) (mems : members) : compact_prod (map (λ it : member, type) mems).
    revert tys; induction mems; simpl; intros.
    { exact tt. }
    destruct mems; simpl.
    - destruct tys.
      + exact tytrue.
      + exact t.
    - destruct tys.
      + exact (tytrue, IHmems []).
      + exact (t, IHmems tys).
  Defined.

  Lemma make_ty_prod_cons2 : forall ty tys m0 m1 mems, make_ty_prod (ty :: tys) (m0 :: m1 :: mems) = (ty, make_ty_prod tys (m1 :: mems)).
  Proof. reflexivity. Qed.

  Opaque field_type.
  Opaque field_offset.

  Definition heap_memory_block β n v :=
    match β with
    | Own => mapsto_memory_block.memory_block Tsh n v
    | Shr => inv mtN (∃ q, ⌜readable_share q⌝ ∧ mapsto_memory_block.memory_block q n v)
    end.

  Definition heap_spacer β (be: Z) (ed: Z) : val -> mpred :=
    if BinInt.Z.eq_dec (ed - be) 0
    then fun _ => emp
    else mapsto_memory_block.at_offset (heap_memory_block β (ed - be)) be.

  Definition heap_withspacer β (be: Z) (ed: Z) P (p: val): mpred :=
    P p ∗ if BinInt.Z.eq_dec (ed - be) 0 then emp else heap_spacer β be ed p.

  Global Instance spacer_persistent be ed v : Persistent (heap_spacer Shr be ed v).
  Proof.
    rewrite /heap_spacer; if_tac; apply _.
  Qed.

  Global Instance withspacer_persistent be ed P v : Persistent (P v) → Persistent (heap_withspacer Shr be ed P v).
  Proof.
    rewrite /heap_withspacer; if_tac; apply _.
  Qed.

  Lemma heap_withspacer_eq : forall be ed P p, heap_withspacer Own be ed P p =
    mapsto_memory_block.withspacer Tsh be ed P p.
  Proof.
    intros; rewrite /heap_withspacer /mapsto_memory_block.withspacer /heap_spacer /mapsto_memory_block.spacer;
      if_tac; try done.
    apply log_normalize.sep_emp.
  Qed.

  Lemma struct_pred_irrel : forall m {A} (P : forall it, A it -> val -> mpred) v p p',
    (forall it v, P it v p = P it v p') -> aggregate_pred.struct_pred m P v p = aggregate_pred.struct_pred m P v p'.
  Proof.
    induction m; intros; first done.
    destruct m.
    - simpl; auto.
    - setoid_rewrite struct_pred_cons2.
      f_equal; auto.
  Qed.

  Lemma proj_compact_prod_cons2 : forall {A} {F : A → Type} a x0 x1 l (v : compact_prod (map F (x0 :: x1 :: l))) d H,
     proj_compact_prod a (x0 :: x1 :: l) v d H =
     match H a x0 with
     | left e => rew <- e in v.1
     | right n => proj_compact_prod a (x1 :: l) v.2 d H
     end.
  Proof.
    intros; rewrite {1}/proj_compact_prod /list_rect.
    destruct (H a x0); subst; done.
  Qed.

  Lemma proj_struct_lookup : forall i m d j tys ty
    (Hnorep : members_no_replicate m = true)
    (Hm : m !! j = Some (get_member i m)) (Htys : tys !! j = Some ty),
    proj_struct i m (make_ty_prod tys m) d = ty.
  Proof.
    intros; rewrite /proj_struct.
    forget (get_member i m) as a.
    generalize dependent j; revert tys; induction m; first done; intros.
    destruct tys; first done.
    destruct m.
    - simpl in *.
      apply list_lookup_singleton_Some in Hm as (-> & ->).
      inv Htys.
      destruct (member_dec a a); subst; try done.
      destruct e; done.
    - rewrite proj_compact_prod_cons2 make_ty_prod_cons2.
      rewrite /members_no_replicate /= in Hnorep.
      destruct (_ || _) eqn: Hout; first done.
      destruct (member_dec a a0); subst.
      + destruct j; inv Htys; inv Hm; first done.
        destruct j; inv H1.
        * rewrite Pos.eqb_refl // in Hout.
        * destruct (id_in_list _ _) eqn: Hid.
          { rewrite orb_true_r // in Hout. }
          apply id_in_list_false in Hid; contradiction Hid.
          rewrite in_map_iff.
          apply elem_of_list_lookup_2, elem_of_list_In in H2; eauto.
      + destruct j; inv Hm; inv Htys; eauto.
  Qed.

  Program Definition struct_pred (i : ident) (tys : list type) : type := {|
    ty_has_op_type := is_struct_ot i tys;
    ty_own β l :=
      <affine> ⌜l `has_layout_loc` (Tstruct i noattr)⌝ ∗ ∃ sl, <affine> ⌜(cenv_cs !! i)%maps = Some sl ∧ length (sl.(co_members)) = length tys⌝ ∗
      aggregate_pred.struct_pred sl.(co_members) (λ m ty,
        heap_withspacer β (field_offset cenv_cs (name_member m) sl.(co_members) + sizeof (field_type (name_member m) sl.(co_members)))
         (field_offset_next cenv_cs (name_member m) sl.(co_members) (co_sizeof sl))
         (mapsto_memory_block.at_offset (λ p, match val2adr p with Some l => l ◁ₗ{β} ty | _ => False end)
            (field_offset cenv_cs (name_member m) sl.(co_members)))) (make_ty_prod tys sl.(co_members)) l;
    ty_own_val cty v :=
      (∃ a (Hcty : cty = Tstruct i a), <affine> ⌜v `has_layout_val` cty⌝ ∗ ∃ sl, <affine> ⌜(cenv_cs !! i)%maps = Some sl ∧ length (sl.(co_members)) = length tys⌝ ∗
       (*[∗ list] v';ty∈reshape (ly_size <$> sl.(sl_members).*2) v;tys, (v' ◁ᵥ ty))%I;*)
       aggregate_pred.struct_pred (get_co i).(co_members) (λ m v _,
         ∃ ty, <affine> ⌜∃ j, sl.(co_members) !! j = Some m ∧ tys !! j = Some ty⌝ ∗ v ◁ᵥ|field_type (name_member m) (get_co i).(co_members)| ty)
         (unfold_reptype (rew Hcty in v)) Vundef);
  |}%I.
  Next Obligation.
    iIntros (?????) "[% [% [%Hsl HP]]]". iFrame "%".
    pose proof (get_co_members_no_replicate i) as Hnorep.
    destruct Hsl as (Hsl & _).
    rewrite /get_co Hsl in Hnorep.
    iApply struct_pred_fupd. iApply (aggregate_pred.struct_pred_ext_derives with "HP"); first done.
    intros.
    exploit (proj_struct_JMeq i0 (co_members sl) (make_ty_prod tys (co_members sl)) (make_ty_prod tys (co_members sl)) d0 d1); try done.
    intros ->%jmeq_lemmas.JMeq_eq.
    rewrite /heap_withspacer /heap_spacer /mapsto_memory_block.at_offset /=.
    iIntros "(Hty & ?)"; iSplitL "Hty"; first by iApply ty_share.
    if_tac; first done.
    iApply inv_alloc. iModIntro. iExists _. iFrame; auto.
  Qed.
  Next Obligation. iIntros (sl tys ot mt l (? & ->)%is_struct_ot_layout) "(?&_)". rewrite has_layout_struct_noattr //. Qed.
  Next Obligation. iIntros (sl tys ot mt v (? & ->)%is_struct_ot_layout) "(% & % & % & _)". done. Qed.
  Next Obligation.
    move => i tys ot mt l /is_struct_ot_forall.
    iIntros (((a & ->) & Hlys)) "Htys". iDestruct "Htys" as (_ sl (Hi & Hcount)) "Htys".
    destruct Hlys as (? & Hi' & Hlys); rewrite Hi' in Hi; inv Hi.
    assert (sl = get_co i) as ->.
    { rewrite /get_co Hi' //. }
    rewrite /has_layout_val /type_is_volatile. setoid_rewrite value_fits_eq; simpl.
    setoid_rewrite mapsto_struct.
    iAssert (∀ mems, ⌜mems = co_members (get_co i)⌝ → ∃ v : compact_prod (map (λ it : member, reptype (field_type (name_member it) mems)) (co_members (get_co i))),
      aggregate_pred.struct_pred (co_members (get_co i))
    (λ (it : member) (v : reptype (field_type (name_member it) mems)),
       mapsto_memory_block.withspacer Tsh
         (field_offset cenv_cs (name_member it) mems +
          sizeof (field_type (name_member it) mems))
         (field_offset_next cenv_cs (name_member it) mems (co_sizeof (get_co i)))
         (mapsto_memory_block.at_offset
            (data_at_rec Tsh (field_type (name_member it) mems) v)
            (field_offset cenv_cs (name_member it) mems))) v (adr2val l) ∗
    <affine> ⌜aggregate_pred.aggregate_pred.struct_Prop (co_members (get_co i))
       (λ it : member, value_fits (field_type (name_member it) mems)) v ∧ false = false⌝ ∗
    <affine> ⌜length (co_members (get_co i)) = length tys⌝ ∗
      aggregate_pred.struct_pred (co_members (get_co i))
        (λ (m : member) (v : reptype (field_type (name_member m) mems)) (_ : val),
           ∃ ty : type, <affine> ⌜∃ j : nat, co_members (get_co i) !! j = Some m ∧ tys !! j = Some ty⌝ ∗
             v ◁ᵥ| field_type (name_member m) mems | ty) v Vundef)%I with "[Htys]" as "Hv".
    2: { iDestruct ("Hv" with "[//]") as (?) "Hv"; iExists (fold_reptype(t := Tstruct i a) v).
         rewrite unfold_fold_reptype.
         iDestruct "Hv" as "($ & $ & % & H)". iExists a, eq_refl; simpl.
         iExists (get_co i); rewrite unfold_fold_reptype; by iFrame. }
    iIntros (? Hmems).
    rewrite -{1}Hmems in Hlys; rewrite -{2 3 4 5}Hmems; clear Hmems.
    pose proof (get_co_members_no_replicate i) as Hnorep.
    iInduction (co_members (get_co i)) as [|m ms] "IH" forall (tys l Hlys Hcount).
    { csimpl; destruct tys; done. }
    inv Hlys. destruct H1.
    rewrite /members_no_replicate /= in Hnorep.
    destruct (id_in_list _ _) eqn: Hm; first done.
    destruct ms.
    - simpl.
      rewrite /heap_withspacer /heap_spacer /mapsto_memory_block.withspacer /mapsto_memory_block.spacer /mapsto_memory_block.at_offset /offset_val /=.
      iDestruct "Htys" as "(Hty & Hspacer)".
      iDestruct (ty_deref with "Hty") as (v) "(Hv & Hty)"; first done.
      iDestruct (ty_size_eq with "Hty") as %(? & _); first done.
      iExists v; iFrame.
      iSplit.
      + if_tac; iFrame.
      + iPureIntro.
        simpl; split3; auto.
        by exists O.
    - setoid_rewrite struct_pred_cons2 at 1.
      iDestruct "Htys" as "((Hty & Hspacer) & Htys)".
      iDestruct (ty_deref with "Hty") as (v) "(Hv & Hty)"; first done.
      iDestruct ("IH" with "[//] [//] [//] Htys") as "(%vs & Hvs & (%Hvs & _) & %Hlen & Htys)"; iClear "IH".
      iDestruct (ty_size_eq with "Hty") as %(? & _); first done.
      iExists (v, vs); setoid_rewrite struct_pred_cons2.
      rewrite -heap_withspacer_eq; iFrame.
      iSplit.
      { iPureIntro; rewrite struct_Prop_cons2 //. }
      iSplit; first by iPureIntro; rewrite /= -Hlen.
      iFrame.
      iSplit.
      + iPureIntro; by exists O.
      + iApply (aggregate_pred.struct_pred_ext_derives with "Htys"); first done.
        intros; do 3 f_equiv.
        * do 2 f_equiv; intros (j & ? & ?); by exists (S j).
        * exploit (proj_struct_JMeq i0 (m0 :: ms) vs vs d0 d1); try done.
          by intros ->%jmeq_lemmas.JMeq_eq.
  Qed.
  Next Obligation.
    move => i tys ot mt l v /is_struct_ot_forall. iIntros (((? & ->) & Hlys) Hly) "Hl".
    iDestruct 1 as (?? Hv sl (Hi & Hcount)) "Htys".
    dependent destruction Hcty; simpl.
    rewrite has_layout_struct_noattr in Hly.
    iSplit => //.
    destruct Hlys as (? & Hi' & Hlys); rewrite Hi' in Hi; inv Hi.
    pose proof (Forall2_length Hlys).
    iExists _; iSplit => //.
    assert (sl = get_co i) as ->.
    { rewrite /get_co Hi' //. }
    rewrite mapsto_struct.
    rewrite (struct_pred_irrel _ _ _ _ l) //.
    iCombine "Hl Htys" as "Htys"; rewrite aggregate_pred.struct_pred_sepcon.
    pose proof (get_co_members_no_replicate i) as Hnorep.
    iApply (aggregate_pred.struct_pred_ext_derives with "Htys"); first done.
    intros f ?? Hf; rewrite -heap_withspacer_eq /heap_withspacer /mapsto_memory_block.at_offset /=; iIntros "((Hl & $) & Hv)".
    iDestruct "Hv" as (? (j & ? & ?)) "Hv".
    eapply (Forall2_lookup_lr _ _ _ j) in Hlys as (? & ?); [|done..].
    erewrite proj_struct_lookup; [|done..].
    iApply (ty_ref with "[%] [Hl] [Hv]"); try done.
    apply (field_compatible_app_inv' [StructField f]), field_compatible_nested_field in Hly; last done.
    rewrite app_nil_r /nested_field_type /nested_field_offset /= in Hly.
    apply compute_in_members_true_iff in Hf; rewrite Hf /= in Hly.
    rewrite name_member_get //.
  Qed.

  Global Instance struct_le : Proper ((=) ==> Forall2 (⊑) ==> (⊑)) struct.
  Proof.
    move => ? sl -> tys1 tys2 Htys.
    have Hlen : length tys1 = length tys2 by apply: Forall2_length.
    constructor.
    - move => β l; rewrite/ty_own/=/offset_of_idx.
      f_equiv. f_equiv; first by move: Htys => /Forall2_length->. f_equiv. clear Hlen.
      elim: (sl_members sl) tys1 tys2 Htys l => // -[m ?] s IH tys1 tys2 Htys l. csimpl.
      f_equiv.
      + do 2 f_equiv. apply default_proper; [done|]. by f_equiv.
      + setoid_rewrite <-shift_loc_assoc_nat; apply IH => //.
        destruct m, Htys => //. by f_equiv.
    - move => v. rewrite/ty_own_val/=. f_equiv. rewrite Hlen. f_equiv. clear Hlen.
      elim: (sl_members sl) v tys1 tys2 Htys => // -[m ?] s IH v tys1 tys2 Htys. csimpl.
      f_equiv.
      + do 2 f_equiv. apply default_proper; [done|]. by f_equiv.
      + apply IH. destruct m, Htys => //. by f_equiv.
  Qed.
  Global Instance struct_proper : Proper ((=) ==> Forall2 (≡) ==> (≡)) struct.
  Proof. move => ??-> ?? Heq. apply type_le_equiv_list; [by apply struct_le|done]. Qed.

  Lemma struct_focus l β sl tys:
    l ◁ₗ{β} struct sl tys -∗ ([∗ list] n;ty∈field_names sl.(sl_members);tys, l at{sl}ₗ n ◁ₗ{β} ty) ∗ (∀ tys',
           ([∗ list] n;ty∈field_names sl.(sl_members);tys', l at{sl}ₗ n ◁ₗ{β} ty) -∗ l ◁ₗ{β} struct sl tys').
  Proof.
    rewrite {1 4}/ty_own/=. iIntros "[$ Hs]". iDestruct "Hs" as (Hcount) "[#Hb Hs]".
    rewrite /GetMemberLoc/offset_of_idx.
    have HND : (NoDup (field_names (sl_members sl))) by eapply bool_decide_unpack, sl_nodup.
    iInduction (sl_members sl) as [|[n ly] ms] "IH" forall (l tys Hcount HND). {
      destruct tys => //. iSplit => //. iIntros (tys') "Htys".
      iDestruct (big_sepL2_nil_inv_l with "Htys") as %->. iFrame. by iSplit.
    }
    csimpl. iDestruct "Hs" as "[Hl Hs]".
    iDestruct (loc_in_bounds_split with "Hb") as "[Hb1 Hb2]".
    setoid_rewrite <-shift_loc_assoc_nat.
    iDestruct ("IH" with "[] [] Hb2 Hs") as "[Hl1 Hs]"; try iPureIntro.
    { by destruct n, tys; naive_solver. }
    { destruct n => //. apply: NoDup_cons_1_2. naive_solver. }
    iClear "IH". destruct n; csimpl.
    - destruct tys => //=. rewrite offset_of_cons; eauto. case_decide => //=. iFrame.
      iSplitL "Hl1". {
        iApply (big_sepL2_impl with "Hl1"). iIntros "!#" (k n ty Hm ?) "Hl".
        move: Hm => /(list_elem_of_lookup_2 _ _ _) ?.
        rewrite offset_of_cons; eauto. case_decide; last by rewrite shift_loc_assoc_nat.
        move: HND => /= /(NoDup_cons_1_1 _ _). set_solver.
      }
      iIntros (tys') "Htys".
      iDestruct (big_sepL2_cons_inv_l with "Htys") as (?? ->)"[H1 Htys]".
      rewrite offset_of_cons; eauto. case_decide => //=. iFrame.
      iDestruct (big_sepL2_length with "Htys") as %<-. iSplitR => //.
      iSplit. { iApply loc_in_bounds_split. eauto. }
      iDestruct ("Hs" with "[Htys]") as (?) "[_ $]".
      iApply (big_sepL2_impl with "Htys"). iIntros "!#" (k n ty Hm ?) "Hl".
      move: Hm => /(list_elem_of_lookup_2 _ _ _) ?.
      rewrite offset_of_cons; eauto. case_decide; last by rewrite shift_loc_assoc_nat.
      move: HND => /= /(NoDup_cons_1_1 _ _). set_solver.
    - iFrame. iSplitL "Hl1". {
        iApply (big_sepL2_impl with "Hl1"). iIntros "!#" (k n ty Hm ?) "Hl".
        move: Hm => /(list_elem_of_lookup_2 _ _ _) ?.
        rewrite offset_of_cons; eauto. case_decide => //. by rewrite shift_loc_assoc_nat.
      }
      iIntros (tys') "Htys".
      iDestruct ("Hs" with "[Htys]") as (?) "[_ $]" => //; last by iSplit.
      iApply (big_sepL2_impl with "Htys"). iIntros "!#" (k n ty Hm ?) "Hl".
      move: Hm => /(list_elem_of_lookup_2 _ _ _) ?.
      rewrite offset_of_cons; eauto. case_decide => //. by rewrite shift_loc_assoc_nat.
  Qed.

  Lemma struct_focus_val v sl tys:
    v ◁ᵥ struct sl tys -∗
     (∃ vs, ([∗ list] v;ty∈vs;tys, v ◁ᵥ ty) ∗ (∀ tys',
           ([∗ list] v;ty∈vs;tys', v ◁ᵥ ty) -∗ v ◁ᵥ struct sl tys')).
  Proof.
    rewrite {1 4}/ty_own_val/=. iIntros "[$ [%Hlen Hs]]".
    iInduction (sl_members sl) as [|[n ly] ms] "IH" forall (v tys Hlen). {
      destruct tys => //. iExists []. iSplit => //. iIntros (tys') "Htys".
      iDestruct (big_sepL2_nil_inv_l with "Htys") as %->. by iFrame.
    }
    csimpl. iDestruct "Hs" as "[Hl Hs]".
    iDestruct ("IH" with "[] Hs") as (vs) "[Hl1 Hs]"; try iPureIntro.
    { by destruct n, tys; naive_solver. }
    iDestruct (big_sepL2_length with "Hl1") as %?.
    iClear "IH". destruct n; csimpl.
    - destruct tys => //=. iExists (_::_). iFrame.
      iIntros (tys') "Htys".
      iDestruct (big_sepL2_cons_inv_l with "Htys") as (? tys'2 ->)"[H1 Htys]".
      iDestruct (big_sepL2_length with "Htys") as %?. iSplit; [iPureIntro; naive_solver lia|].
      simpl. iFrame. iDestruct ("Hs" with "Htys") as (?) "$".
    - iExists _. by iFrame.
  Qed.

  Global Instance struct_loc_in_bounds sl tys β : LocInBounds (struct sl tys) β (ly_size sl).
  Proof.
    constructor. by iIntros (l) "(_&_&?&_)".
  Qed.

  Global Instance struct_alloc_alive sl tys β P `{!TCExists (λ ty, AllocAlive ty β P) tys} :
    AllocAlive (struct sl tys) β P.
  Proof.
    revert select (TCExists _ _).
    rewrite TCExists_Exists Exists_exists => -[x [/(list_elem_of_lookup_1 _ _) [i Hx] ?]].
    constructor. iIntros (l) "HP Hl".
    iDestruct (struct_focus with "Hl") as "[Hl _]".
    iDestruct (big_sepL2_length with "Hl") as %Hlen.
    have [|n Hn] := lookup_lt_is_Some_2 (field_names (sl_members sl)) i.
    { rewrite Hlen. by apply: lookup_lt_Some. }
    iDestruct (big_sepL2_lookup with "Hl") as "Hl" => //.
    iDestruct (alloc_alive_alive with "HP Hl") as "Hl".
    by iApply (alloc_alive_loc_mono with "Hl").
  Qed.

  Lemma struct_mono A M sl tys1 tys2 l β T:
    subsume (l ◁ₗ{β} struct sl tys1) M (λ x : A, l ◁ₗ{β} struct sl (tys2 x)) T :-
      iterate: zip (field_names sl.(sl_members)) tys1 {{e T,
        inhale (l at{sl}ₗ e.1 ◁ₗ{β} e.2); return T}};
      ‖M‖ ∃ x, exhale ⌜length tys1 = length (tys2 x)⌝;
      iterate: zip (field_names sl.(sl_members)) (tys2 x) {{e T,
        exhale (l at{sl}ₗ e.1 ◁ₗ{β} e.2); return T}};
      return T x.
  Proof.
    iIntros "HG Hl". iDestruct (struct_focus with "Hl") as "[Hs Hc]".
    iDestruct (big_sepL2_length with "Hs") as %?.
    pose (INV := (λ i,
      [∗ list] n;ty ∈ drop i (field_names (sl_members sl));drop i tys1, l at{sl}ₗ n ◁ₗ{β} ty)%I).
    iDestruct (iterate_elim0 INV with "HG [Hs] [#]") as "[_ HG]"; unfold INV; clear INV.
    { by rewrite !drop_0. } {
      iIntros "!>" (i x ? (?&?&?&?&?)%lookup_zip_with_Some); simplify_eq/=.
      iIntros "Hinv HT". erewrite drop_S; [|done]. erewrite (drop_S _ _ i); [|done] => /=.
      iDestruct "Hinv" as "[Hl $]". by iApply "HT".
    }
    iMod "HG" as (x Hlen) "HG".
    pose (INV := (λ i,
      [∗ list] n;ty ∈ take i (field_names (sl_members sl));take i (tys2 x), l at{sl}ₗ n ◁ₗ{β} ty)%I).
    iDestruct (iterate_elim0 INV with "HG [] [#]") as "[Hinv HG]"; unfold INV; clear INV.
    { by rewrite !take_0. } {
      iIntros "!>" (i ? ? (?&?&?&?&?)%lookup_zip_with_Some); simplify_eq/=.
      iIntros "Hinv [? $]". erewrite take_S_r; [|done]. erewrite take_S_r; [|done].
      rewrite big_sepL2_snoc. iFrame.
    }
    rewrite !length_zip_with !take_ge; [|lia..]. iModIntro. iFrame.
    by iApply "Hc".
  Qed.
  Definition struct_mono_inst := [instance struct_mono].
  Global Existing Instance struct_mono_inst.

  Lemma struct_mono_val A M sl tys1 tys2 v T:
    subsume (v ◁ᵥ struct sl tys1) M (λ x : A, v ◁ᵥ struct sl (tys2 x)) T :-
      vs ← iterate: tys1 with [] {{e T vs, ∀ v, inhale (v ◁ᵥ e); return T (vs ++ [v])}};
      ‖M‖ ∃ x, exhale ⌜length tys1 = length (tys2 x)⌝;
      iterate: zip vs (tys2 x) {{e T, exhale (e.1 ◁ᵥ e.2); return T}};
      return T x.
  Proof.
    iIntros "HG Hl". iDestruct (struct_focus_val with "Hl") as (vs) "[Hs Hc]".
    iDestruct (big_sepL2_length with "Hs") as %Hlen.
    pose (INV := (λ i vs', ⌜vs' = take i vs⌝ ∗
      [∗ list] v;ty ∈ drop i vs;drop i tys1, v ◁ᵥ ty)%I).
    iDestruct (iterate_elim1 INV with "HG [Hs] [#]") as (vs') "[[% ?] HG]"; unfold INV; clear INV.
    { rewrite take_0 !drop_0. by iFrame. } {
      iIntros "!>" (i x ? vs' ?). iIntros "[-> Hinv] HT".
      have [|??]:= lookup_lt_is_Some_2 vs i. { rewrite Hlen. by apply: lookup_lt_Some. }
      erewrite drop_S; [|done]. erewrite (drop_S _ _ i); [|done] => /=.
      iDestruct "Hinv" as "[Hl $]". iDestruct ("HT" with "[$]") as "HT". iExists _. iFrame.
      by erewrite take_S_r.
    }
    iMod "HG" as (x Hlen2) "HG". subst.
    pose (INV := (λ i,
      [∗ list] v;ty ∈ take i vs;take i (tys2 x), v ◁ᵥ ty)%I).
    iDestruct (iterate_elim0 INV with "HG [] [#]") as "[Hinv HG]"; unfold INV; clear INV.
    { by rewrite !take_0. } {
      iIntros "!>" (i ? ? (?&?&?&Hvs&?)%lookup_zip_with_Some); simplify_eq/=.
      iIntros "Hinv [? $]". rewrite lookup_take_lt in Hvs. 2: { rewrite Hlen2. by apply: lookup_lt_Some. }
      erewrite take_S_r; [|done]. erewrite take_S_r; [|done].
      rewrite big_sepL2_snoc. iFrame.
    }
    rewrite !length_zip_with !take_ge; [|lia..]. iModIntro. iFrame.
    by iApply "Hc".
  Qed.
  Definition struct_mono_val_inst := [instance struct_mono_val].
  Global Existing Instance struct_mono_val_inst.

  Lemma type_place_struct K β1 tys sl n l T :
    (∃ i ty1, ⌜field_index_of sl.(sl_members) n = Some i⌝ ∗
    ⌜tys !! i = Some ty1⌝ ∗
    typed_place K (l at{sl}ₗ n) β1 ty1 (λ l2 β ty2 typ, T l2 β ty2 (λ t, struct sl (<[i := (typ t)]> tys))))
    ⊢ typed_place (GetMemberPCtx sl n :: K) l β1 (struct sl tys) T.
  Proof.
    iDestruct 1 as (i ty1 Hi Hn) "HP".
    move: (Hi) => /field_index_of_to_index_of[? Hi2].
    iIntros (Φ) "[% [% [#Hb Hs]]] HΦ" => /=.
    iApply wp_get_member; [by apply val_to_of_loc|by eauto|done|].
    iIntros "!#". iExists _. iSplit => //.
    iDestruct (big_sepL_insert_acc with "Hs") as "[Hl Hs]" => //=.
    1: by eapply pad_struct_lookup_field.
    rewrite /GetMemberLoc/offset_of Hi2/=.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Hc HT".
    iApply ("HΦ" with "Hl' [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    iDestruct ("Hs" with "Hty") as "Hs". iSplitR => //. iSplitR; first by rewrite length_insert.
    iFrame "Hb". erewrite pad_struct_insert_field => //. have := field_index_of_leq _ _ _ Hi. lia.
  Qed.
  Definition type_place_struct_inst := [instance type_place_struct].
  Global Existing Instance type_place_struct_inst | 10.

  (* Ail fills in the missing elements in fs, so we can assume that
  the lookup will always succeed. This is nice, because otherwise we
  would get a quadractic blowup when simiplifying the foldr. *)
  Lemma type_struct_init_syn sl fs T:
    typed_val_expr (StructInit sl fs) T :-
      tys ← iterate: (field_members sl.(sl_members)) with [] {{ '(n, ly) f tys,
        ∃ e, exhale ⌜(list_to_map fs : gmap _ _) !! n = Some e⌝;
        _, ty ← {typed_val_expr e};
        exhale ⌜ty.(ty_has_op_type) (UntypedOp ly) MCNone⌝;
        return f (tys ++ [ty])}};
      ∀ v, return T v (struct sl tys).
  Proof.
    liFromSyntax. iIntros "He" (Φ) "HΦ". iApply wp_struct_init.
    iAssert ([∗ list] v';ty∈[];pad_struct ([@{option var_name * layout}]) [] (λ ly, uninit ly), (v' ◁ᵥ ty))%I as "-#Hvs". 1: done.
    have : [] ++ sl.(sl_members) = sl.(sl_members) by simplify_list_eq.
    have : [] = reshape (ly_size <$> (snd <$> ([] : field_list))) [@{mbyte}] by [].
    have : length (@nil mbyte) = sum_list (ly_size <$> (snd <$> ([] : field_list))) by [].
    have : length (field_names []) = length [@{type}] by [].
    move: {1 3 4}(@nil type) => tys.
    move: {1 2 4}(@nil val) => vs.
    move: {1 2}(@nil (mbyte)) => v.
    move: {1 2 3 4 5}(@nil (option var_name * layout)) => s.
    move: {1 3 4}(sl_members sl) => slm Hf Hv Hvs Hs.
    iInduction (slm) as [|[n ?] ms] "IH" forall (vs tys v s Hs Hvs Hv Hf); csimpl.
    - iDestruct ("He" $! (mjoin vs)) as "HT". iApply ("HΦ" with "[-HT] HT"). simplify_list_eq.
      rewrite {2}/ty_own_val/=/layout_of{3}/ly_size.
      rewrite join_reshape // ?length_fmap//. by iFrame.
    - rewrite cons_middle assoc in Hs. destruct n => /=.
      + iDestruct "He" as (e ->) "He". iApply "He". iIntros (v1 ty) "Hv [% Hf]".
        iDestruct (ty_size_eq with "Hv") as %Hsz; [done|].
        iApply ("IH" $! _ _ (v ++ v1) with "[//] [] [] [] Hf HΦ");
          try iPureIntro; rewrite ?fmap_app ?pad_struct_snoc_Some ?length_fmap //.
        * by rewrite /= reshape_app take_app_length' ?drop_app_length' /= ?take_ge ?Hsz; subst.
        * rewrite length_app sum_list_with_app /= Hsz -Hv/=; lia.
        * by rewrite /field_names omap_app !length_app Hf.
        * iApply (big_sepL2_app with "Hvs"). by iFrame.
      + iApply wp_value.
        iApply ("IH" $! _ _ (v ++ replicate (ly_size l) ☠%V) with "[//] [] [] [] He HΦ");
          try iPureIntro; rewrite ?fmap_app ?pad_struct_snoc_None.
        * by rewrite reshape_app take_app_length' ?drop_app_length' /= ?take_ge ?Hsz ?length_replicate; subst.
        * rewrite length_app sum_list_with_app Hv length_replicate /=. lia.
        * by rewrite /field_names omap_app !length_app Hf.
        * iApply (big_sepL2_app with "Hvs"). simpl. iSplit => //. unfold bytewise at 2; simpl_type. iPureIntro.
          split; first by rewrite /has_layout_val length_replicate.
          by apply Forall_forall.
  Qed.
  Lemma type_struct_init : [type_from_syntax type_struct_init_syn].
  Proof. exact type_struct_init_syn. Qed.


  Lemma uninit_struct_equiv l β (s : struct_layout) :
    (l ◁ₗ{β} uninit s) ⊣⊢ (l ◁ₗ{β} struct s (uninit <$> omap (λ '(n, ly), const ly <$> n) s.(sl_members))).
  Proof.
    rewrite /layout_of/struct{1 2}/ty_own/offset_of_idx/=.
    iSplit.
    - iDestruct 1 as (v Hv Hl _) "Hl". iSplit => //. iSplit.
      { iPureIntro. rewrite length_fmap. by apply omap_length_eq => i [[?|]?]. }
      have {}Hl := check_fields_aligned_alt_correct _ _ Hl.
      rewrite /has_layout_val{1}/ly_size in Hv.
      iSplit. { iApply loc_in_bounds_shorten; last by iApply heap_mapsto_own_state_loc_in_bounds. lia. }
      iInduction (sl_members s) as [|[n ly] ms] "IH" forall (v l Hl Hv) => //; csimpl in *.
      rewrite shift_loc_0. setoid_rewrite <-shift_loc_assoc_nat. move: Hl => [??].
      have Hlen: (length (take (ly_size ly) v) = ly_size ly) by rewrite length_take_le ?Hv//; cbn; lia.
      rewrite -(take_drop ly.(ly_size) v).
      iDestruct (heap_mapsto_own_state_app with "Hl") as "[Hl Hr]". rewrite Hlen.
      iSplitL "Hl"; destruct n; try by [iExists _; iFrame; rewrite Forall_forall]; iApply "IH" => //;
      try rewrite length_drop; try iPureIntro; lia.
    - iIntros "[$ Hl]". iDestruct "Hl" as (_) "[#Hb Hl]".
      rewrite /has_layout_val{2}/ly_size.
      iInduction (sl_members s) as [|[n ly] ms] "IH" forall (l) => //; csimpl in *.
      { iExists []. rewrite Forall_nil. repeat iSplit => //. by rewrite heap_mapsto_own_state_nil. }
      rewrite shift_loc_0. setoid_rewrite <-shift_loc_assoc_nat.
      iDestruct "Hl" as "[Hl Hs]".
      iDestruct (loc_in_bounds_split with "Hb") as "[Hb1 Hb2]".
      destruct n; csimpl.
      all: rewrite /ty_own/=; iDestruct "Hl" as (v1 Hv1 Hl _) "Hl".
      all: iDestruct ("IH" with "Hb2 Hs") as (v2 Hv2 _) "Hv".
      all: iExists (v1 ++ v2).
      all: rewrite heap_mapsto_own_state_app length_app Hv1 Hv2.
      all: rewrite Forall_app !Forall_forall.
      all: by iFrame.
  Qed.

  Lemma uninit_struct_simpl_hyp l β (s : struct_layout) M T:
    (l ◁ₗ{β} (struct s (uninit <$> omap (λ '(n, ly), const ly <$> n) s.(sl_members))) -∗ ‖M‖ T)
    ⊢ simplify_hyp (l ◁ₗ{β} uninit s) M T.
  Proof. iIntros "HT Hl". rewrite uninit_struct_equiv. by iApply "HT". Qed.
  Definition uninit_struct_simpl_hyp_inst := [instance uninit_struct_simpl_hyp with 0%N].
  Global Existing Instance uninit_struct_simpl_hyp_inst.

  Lemma uninit_struct_simpl_goal l β (s : struct_layout) M T:
    l ◁ₗ{β} (struct s (uninit <$> omap (λ '(n, ly), const ly <$> n) s.(sl_members))) ∗ T
    ⊢ simplify_goal M (l ◁ₗ{β} uninit s) T.
  Proof. iIntros "[? $] !>". by rewrite uninit_struct_equiv. Qed.
  Definition uninit_struct_simpl_goal_inst := [instance uninit_struct_simpl_goal with 50%N].
  Global Existing Instance uninit_struct_simpl_goal_inst.

  Lemma subsume_struct_uninit A M β sl ly tys l T :
    subsume (l ◁ₗ{β} struct sl tys) M (λ x : A, l ◁ₗ{β} uninit ly) T :-
      exhale ⌜ly = layout_of sl⌝;
      x ← {subsume (l ◁ₗ{β} struct sl tys) M (λ x : A,
             l ◁ₗ{β} struct sl (uninit <$> omap (λ '(n, ly0), const ly0 <$> n) (sl_members sl)))};
      return T x.
  Proof.
    iIntros "[-> Ht] Hstruct". iMod ("Ht" with "Hstruct") as "[%x Ht]".
    iModIntro. iExists x. by rewrite uninit_struct_equiv.
  Qed.
  Definition subsume_struct_uninit_inst := [instance subsume_struct_uninit].
  Global Existing Instance subsume_struct_uninit_inst.

End struct.
Global Typeclasses Opaque struct.