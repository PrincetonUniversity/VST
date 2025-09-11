From iris.algebra Require Import list.
From VST.typing Require Export type.
From VST.typing Require Import programs bytes.
From VST.typing Require Import type_options.

Section struct.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* Should the struct type be indexed by a name or a composite (CompCert's analogue of struct_layout)? A name, because
     that's where has_layout_loc is defined (on Ctypes.type). *)

  (* We state the sidecondition using foldr instead of Forall since this is faster to solve for the automation. *)
  Definition is_struct_ot (i : ident) (tys : list type) (ot : Ctypes.type) (mt : memcast_compat_type) :=
    match cenv_cs !! i, ot with
    | Some sl, Tstruct i' _ => sl.(co_su) = Struct ∧ length (sl.(co_members)) = length tys ∧
        i' = i ∧ mt ≠ MCId ∧
        foldr (λ x, and (x.1.(ty_has_op_type) (type_member x.2) mt)) True (zip tys sl.(co_members))
    | _, _ => False
    end.

  Lemma is_struct_ot_layout i tys ot mt:
    is_struct_ot i tys ot mt → ∃ a, ot = Tstruct i a.
  Proof. move => [?]. destruct ot => //; naive_solver. Qed.

  Lemma is_struct_ot_forall i tys ot mt:
    is_struct_ot i tys ot mt →
    (∃ a, ot = Tstruct i a) ∧
    Forall2 (λ m ty, ∃ mt, ty.(ty_has_op_type) (type_member m) mt) sl.(sl_members) tys.
  Proof.
    move => [Hlen]. destruct ot => //.
    - move => [-> [? [? /Forall_fold_right Hall]]]. split; [done|].
      apply: Forall2_same_length_lookup_2. { by rewrite pad_struct_length. }
      move => i [n ly] ty Hm /pad_struct_lookup_Some[|?[?[Hl1 Hor]]]; simplify_eq.
      { lia. }
      rewrite Hl1 in Hm. simplify_eq.
      move: Hor => [[??] |[??]]; simplify_eq/=. 2: eexists (UntypedOp _), MCNone; naive_solver.
      destruct n as [n|] => //.
      have [|ot ?]:= lookup_lt_is_Some_2 ots (field_idx_of_idx (sl_members sl) i).
      { have := field_idx_of_idx_bound sl i n ly ltac:(done). lia. }
      move: Hall => /(Forall_lookup_1 _ _ (field_idx_of_idx (sl_members sl) i) (ty, (n, ly), ot)) [|/=?<-].
      2: naive_solver.
      apply/lookup_zip_with_Some. eexists (_, _), _. split_and!; [done| |done].
      apply/lookup_zip_with_Some. eexists _, _. split_and!; [done..|].
      by apply: field_members_idx_lookup.
    - move => [-> /Forall_fold_right Hfold]. split; [done|].
      elim: (sl_members sl) tys Hlen Hfold; clear; [done|].
      move => [n ly] s IH tys//=?. destruct n; simplify_eq/=.
      + destruct tys => //. move => /Forall_cons/=[? /IH?]. constructor => //; [|naive_solver].
        eexists _, _. split; [|done]. done.
      + move => /IH. constructor; [| naive_solver]. eexists (UntypedOp ly), MCNone. done.
  Qed.

  Program Definition struct_pred (i : ident) (tys : list type) : type := {|
    ty_has_op_type := is_struct_ot i tys;
    ty_own β l :=
      <affine> ⌜l `has_layout_loc` (Tstruct i noattr)⌝ ∗ ∃ sl, <affine> ⌜cenv_cs !! i = Some sl ∧ length (sl.(co_members)) = length tys⌝ ∗
      (*loc_in_bounds l (sum_list (ly_size <$> (sl_members sl).*2)) ∗*)
      [∗ list] ty;m∈tys;sl.(co_members),
        (field_offset cenv_cs (name_member m) sl.(co_members)) ◁ₗ{β} ty;
    ty_own_val cty v :=
      (<affine> ⌜cty = Tstruct i noattr ∧ v `has_layout_val` (Tstruct i noattr)⌝ ∗ ∃ sl, <affine> ⌜cenv_cs !! i = Some sl ∧ length (sl.(co_members)) = length tys⌝ ∗
       (*[∗ list] v';ty∈reshape (ly_size <$> sl.(sl_members).*2) v;tys, (v' ◁ᵥ ty))%I;*)
       aggregate_pred.struct_pred sl.(co_members) (λ m _ v, v ◁ᵥ|type_member m| ty) v;
  |}%I.
  Next Obligation.
    iIntros (?????) "[% [% [#Hb HP]]]". do 3 iSplitR => //.
    iApply big_sepL_fupd. iApply (big_sepL_impl with "HP").
    iIntros "!#" (???) => /=. by iApply ty_share.
  Qed.
  Next Obligation. iIntros (sl tys ot mt l ->%is_struct_ot_layout) "(?&_)". done. Qed.
  Next Obligation. iIntros (sl tys ot mt v ->%is_struct_ot_layout) "(?&_)". done. Qed.
  Next Obligation.
    move => sl tys ot mt l /is_struct_ot_forall[_ ].
    iIntros (Hlys) "Htys". iDestruct "Htys" as (_ Hcount) "[#Hb Htys]".
    rewrite /=/layout_of{1}/has_layout_val{2}/ly_size.
    iInduction (sl_members sl) as [|[n ly] ms] "IH" forall (tys l Hlys Hcount); csimpl.
    { iExists []. iSplitR; first by iApply heap_mapsto_nil. iSplit => //. }
    move: Hlys => /=. intros (ty & tys' & [?[?[??]]] &?&[=])%Forall2_cons_inv_l.
    rewrite shift_loc_0. iDestruct "Htys" as "[Hty Htys]". cbn.
    iDestruct (loc_in_bounds_split with "Hb") as "[Hb1 Hb2]".
    setoid_rewrite <-shift_loc_assoc_nat.
    destruct n => /=.
    1: destruct tys => //; simplify_eq/=.
    all: iDestruct (ty_deref with "Hty") as (v') "[Hl Hty]"; [done|].
    all: iDestruct (ty_size_eq with "Hty") as %Hszv; [done|].
    all: iDestruct ("IH" $! _ with "[] [] Hb2 Htys") as (vs') "(Hl' & Hsz & Hf & Htys)";
      try iPureIntro; simplify_eq/= => //.
    all: iDestruct "Hsz" as %Hsz; iDestruct "Hf" as %Hf.
    all: iExists (v' ++ vs').
    all: rewrite heap_mapsto_app -Hsz take_app_length' // drop_app_length' // length_app; iFrame.
    all: rewrite Hszv; iFrame "Hl'".
    all: iPureIntro; eauto with lia.
    Unshelve. all: apply: MCNone.
  Qed.
  Next Obligation.
    move => sl tys ot mt l v /is_struct_ot_forall[-> ]. iIntros (Hlys Hly) "Hl".
    rewrite /layout_of/has_layout_val{1}/ly_size /=.
    iDestruct 1 as (Hv Hcount) "Htys". do 2 iSplitR => //.
    have {}Hly := check_fields_aligned_alt_correct _ _ Hly.
    iSplit. { rewrite -Hv. by iApply heap_mapsto_loc_in_bounds. }
    iInduction (sl_members sl) as [|[n ly] ms] "IH" forall (tys l v Hlys Hv Hcount Hly); csimpl in * => //.
    iDestruct "Htys" as "[Hty Htys]".
    move: Hlys. intros [[?[?[??]]] ?]%Forall2_cons. move: Hly => [??].
    rewrite -(take_drop (ly_size ly) v).
    rewrite shift_loc_0 heap_mapsto_app take_app_length' ?length_take_le // ?Hv; try by cbn; lia.
    iDestruct "Hl" as "[Hl Hl']". cbn. simplify_eq/=.
    setoid_rewrite <-shift_loc_assoc_nat.
    iSplitR "Htys Hl'".
    - iClear "IH".
      destruct n; [destruct tys => //|] => /=; iDestruct (ty_ref with "[] Hl Hty") as "$" => //.
    - destruct n => /=; rewrite -?fmap_tail; iApply ("IH" with "[] [] [] [] Hl' [Htys]") => //;
        iClear "IH"; try iPureIntro; rewrite ?length_drop; try lia.
      all: try by rewrite Hv /struct_size/offset_of_idx; csimpl; lia.
      1: destruct tys; naive_solver.
      all: rewrite drop_app_length' ?length_take// Hv; cbn; lia.
  Qed.
  Next Obligation.
    iIntros (sl tys v ot mt st Hot). apply: mem_cast_compat_Untyped => ?.
    destruct ot => //; try by destruct Hot.
    destruct mt => //; try by destruct Hot; naive_solver.
    move: Hot => [? [-> [? [? /Forall_fold_right Hall]]]].
    iIntros "(%&%&Htys)". iSplit. { by rewrite /has_layout_val mem_cast_length. } iSplit. { done. }
    iAssert ⌜∀ i v' n ly,
         reshape (ly_size <$> (sl_members sl).*2) v !! i = Some v' →
         sl_members sl !! i = Some (Some n, ly) → v' `has_layout_val` ly⌝%I as %?. {
      iIntros (i v' n ly Hv' Hly).
      have [|ty ?]:= lookup_lt_is_Some_2 tys (field_idx_of_idx (sl_members sl) i).
      { have := field_idx_of_idx_bound sl i _ _ ltac:(done). lia. }
      iDestruct (big_sepL2_lookup with "Htys") as "Hv"; [done| |].
      { apply/pad_struct_lookup_Some. { done. } naive_solver. }
      have [|ot ?]:= lookup_lt_is_Some_2 ots (field_idx_of_idx (sl_members sl) i).
      { have := field_idx_of_idx_bound sl i _ _ ltac:(done). lia. }
      move: Hall => /(Forall_lookup_1 _ _ (field_idx_of_idx (sl_members sl) i) (ty, (n, ly), ot)) [|/=?<-].
      { apply/lookup_zip_with_Some. eexists (_, _), _. split_and!; [done| |done].
        apply/lookup_zip_with_Some. eexists _, _. split_and!; [done..|]. by apply: field_members_idx_lookup. }
      by iApply (ty_size_eq with "Hv").
    }
    iApply (big_sepL2_impl' with "Htys"); [by rewrite !length_reshape |done|].
    iIntros "!>" (k v1 ty1 v2 ty2 Hv1 Hty1 Hv2 Hty2) "Hv"; simplify_eq.
    rewrite mem_cast_struct_reshape // in Hv2; [|congruence].
    move: Hv2 => /lookup_zip_with_Some [?[?[?[Hpad Hv']]]]. simplify_eq.
    rewrite Hv1 in Hv'. simplify_eq.
    move: Hty1 => /pad_struct_lookup_Some[|n[?[? Hor1]]]. { done. }
    move: Hpad => /pad_struct_lookup_Some[|?[?[? Hor2]]]. { rewrite length_fmap. congruence. } simplify_eq.
    destruct Hor1 as [[??] |[??]], Hor2 as [[? Hl] |[??]]; simplify_eq.
    - rewrite list_lookup_fmap in Hl. move: Hl => /fmap_Some[ot [??]]. simplify_eq.
      iApply ty_memcast_compat_copy; [|done]. destruct n as [n|] => //.
      have [|p ?]:= lookup_lt_is_Some_2 (field_members (sl_members sl)) (field_idx_of_idx (sl_members sl) k).
      { have := field_idx_of_idx_bound sl k _ _ ltac:(done). rewrite field_members_length. lia. }
      move: Hall => /(Forall_lookup_1 _ _ (field_idx_of_idx (sl_members sl) k) (ty1, p, ot))[|??]. 2: naive_solver.
      apply/lookup_zip_with_Some. eexists (_, _), _. split_and!; [done| |done].
      apply/lookup_zip_with_Some. eexists _, _. naive_solver.
    - unfold bytewise; simpl_type. iPureIntro.
      rewrite /has_layout_val length_replicate. split; [done|]. by apply: Forall_true.
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