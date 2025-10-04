Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs bytes (*padded*) struct int.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.

Section union.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (*** active_union *)
  Program Definition active_union (i : ident) (f : ident) (ty : type) : type := {|
    ty_own β l := ∃ m, <affine> ⌜∃ ul, (cenv_cs !! i)%maps = Some ul ∧ get_member f ul.(co_members) = m⌝ ∗
      l ◁ₗ{β} ty ∗ heap_spacer β (sizeof (type_member m)) (co_sizeof (get_co i)) l;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ _ := True;
  |}%I.
  Solve Obligations with try done.
  Next Obligation.
    iIntros (ul f ty l E ?). iDestruct 1 as (ly ?) "Hp". iExists _. iSplitR => //.
    iDestruct "Hp" as "(H & ?)"; iSplitL "H"; first by iApply ty_share.
    rewrite /heap_spacer /mapsto_memory_block.at_offset. if_tac; first done.
    iApply inv_alloc. iModIntro. iExists _. iFrame; auto.
  Qed.

(*  Lemma type_place_uninit_union K β ul n l T:
    (∃ ly, ⌜layout_of_union_member n ul = Some ly⌝ ∗
    typed_place (GetMemberUnionPCtx ul n :: K) l β (active_union ul n (uninit ly)) T)
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l β (uninit ul) T.
  Proof.
    iDestruct 1 as (ly Hly) "HP".
    iIntros (Φ) "Hs HΦ" => /=.
    iApply ("HP" with "[Hs] HΦ").
    iExists _. iSplit => //.
    iApply (apply_subsume_place_true with "Hs"). iApply subsume_uninit_padded.
    iExists tt. iSplit => //. iPureIntro.
    split; apply max_list_elem_of_le; apply elem_of_list_fmap_1; by apply: layout_of_union_member_in_ul.
  Qed.
  Definition type_place_uninit_union_inst := [instance type_place_uninit_union].
  Global Existing Instance type_place_uninit_union_inst.

  Lemma type_place_active_union K β ul n l ty T:
    typed_place K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, active_union ul n (typ t)))
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l β (active_union ul n ty) T.
  Proof.
    iIntros "HP" (Φ) "Hs HΦ" => /=.
    iDestruct "Hs" as (ly ?) "Hpad".
    rewrite /padded. iDestruct "Hpad" as (??) "[Hb [Hty Hpad]]".
    iApply (wp_get_member_union with "[#//]"). 1: by apply val_to_of_loc.
    iExists _. iSplit => //.
    iApply ("HP" with "[Hty]"). 1: by rewrite /GetMemberUnionLoc.
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    iExists _. iSplitR => //. rewrite /padded/GetMemberUnionLoc. by iFrame.
  Qed.
  Definition type_place_active_union_inst := [instance type_place_active_union].
  Global Existing Instance type_place_active_union_inst. *)

End union.
  (*** tagged union *)
  (*** tunion_info *)
Record tunion_info `{!typeG OK_ty Σ} {cs : compspecs} {A : Type} := {
  ti_base_layout : ident;
  ti_tag_field_name : ident;
  ti_union_field_name : ident;
  ti_union_layout : ident;
  ti_tag : A → nat;
  ti_type : A → type;

  ti_base_layout_members : (get_co ti_base_layout).(co_members) = [Member_plain ti_tag_field_name size_t; Member_plain ti_union_field_name (Tunion ti_union_layout noattr)];
  ti_tags_valid r : is_Some ((get_co ti_union_layout).(co_members) !! ti_tag r);
}.
Arguments tunion_info {_ _ _ _} _.

Section union.
  Context `{!typeG OK_ty Σ} {cs : compspecs} {A : Type}.

  Definition ti_member (ti : tunion_info A) (r : A) :=
    (option.default (Member_plain 1%positive Tvoid) ((get_co ti.(ti_union_layout)).(co_members) !! ti.(ti_tag) r)).

(*  Lemma index_of_ti_member ti (x : A):
    index_of_union (ti_member ti x).1 (ti_union_layout ti) = Some (ti.(ti_tag) x).
  Proof.
    rewrite /ti_member.
    destruct (ti_tags_valid ti x) as [[n ly] Heq]. rewrite Heq /=.
    by apply: index_of_union_lookup.
  Qed. *)

  (*** tag *)
  Program Definition tunion_tag (ti : tunion_info A) (x : A) : type := {|
    ty_has_op_type ot mt := ot = size_t;
    ty_own β l := l ◁ₗ{β}ti.(ti_tag) x @ int size_t;
    ty_own_val cty v := v ◁ᵥ|cty| ti.(ti_tag) x @ int size_t;
  |}%I.
  Next Obligation. iIntros (?????). by iApply ty_share. Qed.
  Next Obligation. iIntros (?????->) "Hl". by iApply (ty_aligned _ _ MCNone with "Hl").  Qed.
  Next Obligation. iIntros (?????->) "Hv". by iDestruct (ty_size_eq _ _ MCNone with "Hv") as %?. Qed.
  Next Obligation. iIntros (??????) => /=. by apply: ty_deref. Qed.
  Next Obligation. iIntros (??????->?) "Hl Hv" => /=. by iApply (ty_ref _ _ MCNone with "[] Hl Hv"). Qed.
  (* Next Obligation. iIntros (???????) "Hv" => /=. by iApply (ty_memcast_compat (_ @ int size_t) with "[Hv]"). Qed. *)

  Global Program Instance copyable_tunion_tag ti x : Copyable size_t (tunion_tag ti x).
  Next Obligation. move => *. unfold tunion_tag; simpl_type.
    rewrite /ty_own_val_at /ty_own_val /=. apply _. Qed.
  Next Obligation. move => *. unfold tunion_tag; simpl_type.
    rewrite /ty_own_val_at /ty_own_val /=. apply _. Qed.
  Next Obligation. move => *. unfold tunion_tag; simpl_type. apply _. Qed.
  Next Obligation.
    rewrite /ty_own/ty_own_val/= => ?????/=.
    iIntros "Hl". iMod (copy_shr_acc _ _ with "Hl") as (???) "Hc" => //.
    iSplitR => //. iExists _, _. by iFrame.
  Qed.

  Lemma subsume_int_tunion_tag B ti x (n : Z) l β T:
    (∃ y, <affine> ⌜ti.(ti_tag) (x y) =@{Z} n⌝ ∗ T y)
    ⊢ subsume (l ◁ₗ{β} n @ int size_t) (λ y : B, l ◁ₗ{β} tunion_tag ti (x y)) T.
  Proof. iIntros "[% [<- ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_int_tunion_tag_inst := [instance subsume_int_tunion_tag].
  Global Existing Instance subsume_int_tunion_tag_inst.

  Lemma subsume_tunion_tag B ti x1 x2 l β T:
    (∃ y, <affine> ⌜ti.(ti_tag) x1 = ti.(ti_tag) (x2 y)⌝ ∗ T y)
    ⊢ subsume (l ◁ₗ{β} tunion_tag ti x1) (λ y : B, l ◁ₗ{β} tunion_tag ti (x2 y)) T.
  Proof. rewrite /ty_own/=. iIntros "[% [-> ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_tunion_tag_inst := [instance subsume_tunion_tag].
  Global Existing Instance subsume_tunion_tag_inst.

  Inductive trace_union :=
  | TraceUnion (info : tunion_info A).

  Lemma type_binop_tunion_tag_int ge op it it' ti x v1 n v2 T:
    case_destruct x (λ x' _,
        li_trace (TraceUnion ti, x') (typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|size_t| ti.(ti_tag) x' @ int size_t⎤ v2 ⎡v2 ◁ᵥₐₗ|it| n @ int it⎤ op size_t it it' T))
    ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|size_t| tunion_tag ti x⎤ v2 ⎡v2 ◁ᵥₐₗ|it| n @ int it⎤ op size_t it it' T.
  Proof. iDestruct 1 as (?) "?". by rewrite /(ty_own_val (tunion_tag _ _))/=. Qed.
  Definition type_binop_tunion_tag_int_eq_inst ge := [instance type_binop_tunion_tag_int ge Cop.Oeq].
  Global Existing Instance type_binop_tunion_tag_int_eq_inst.
  Definition type_binop_tunion_tag_int_ne_inst ge := [instance type_binop_tunion_tag_int ge Cop.One].
  Global Existing Instance type_binop_tunion_tag_int_ne_inst.
  Definition type_binop_tunion_tag_int_gt_inst ge := [instance type_binop_tunion_tag_int ge Cop.Ogt].
  Global Existing Instance type_binop_tunion_tag_int_gt_inst.
  Definition type_binop_tunion_tag_int_lt_inst ge := [instance type_binop_tunion_tag_int ge Cop.Olt].
  Global Existing Instance type_binop_tunion_tag_int_lt_inst.
  Definition type_binop_tunion_tag_int_ge_inst ge := [instance type_binop_tunion_tag_int ge Cop.Oge].
  Global Existing Instance type_binop_tunion_tag_int_ge_inst.
  Definition type_binop_tunion_tag_int_le_inst ge := [instance type_binop_tunion_tag_int ge Cop.Ole].
  Global Existing Instance type_binop_tunion_tag_int_le_inst.


  (*** variant *)
  Program Definition variant (ti : tunion_info A) (x : A) (ty : type) : type := {|
    ty_has_op_type ot mt := (∃ a, ot = Tunion ti.(ti_union_layout) a) /\ ty.(ty_has_op_type) (type_member (ti_member ti x)) MCNone;
    ty_own β l := (l ◁ₗ{β} ty ∗ heap_spacer β (sizeof (type_member (ti_member ti x))) (sizeof (Tunion ti.(ti_union_layout) noattr)) l)%I;
    ty_own_val cty v := (v ◁ᵥ|cty| (*(padded ty (ti_member ti x).2 (ul_layout ti.(ti_union_layout)))*) ty)%I;
    (* Do we need the padding in ty_own_val? *)
  |}.
  Next Obligation. iIntros (??????) "(H & ?)". iSplitL "H"; first by iApply ty_share.
    rewrite /heap_spacer /mapsto_memory_block.at_offset. if_tac; first done.
    iApply inv_alloc. iModIntro. iExists _. iFrame; auto.
  Qed.
  Next Obligation. iIntros (?????? ((? & ->) & ?)) "(Hv & _)". iDestruct (ty_aligned _ _ _ with "Hv") as %?; first done.
    iPureIntro. simpl.
  Qed.
  Next Obligation. iIntros (???????) "Hv". by iDestruct (ty_size_eq with "Hv") as %?. Qed.
  Next Obligation. iIntros (???????) => /=. by apply: ty_deref. Qed.
  Next Obligation. iIntros (?????????) "Hl Hv" => /=. by iApply (ty_ref with "[] Hl Hv"). Qed.
  Next Obligation. iIntros (????????) "Hv". by iApply (ty_memcast_compat with "Hv"). Qed.

  Lemma subsume_active_union_variant B ti ul x l β ty1 ty2 n T:
    (l at_union{ul}ₗ n ◁ₗ{β} ty1 -∗
      ∃ y, ⌜ti.(ti_union_layout) = ul⌝ ∗ ⌜(ti_member ti (x y)).1 = n⌝ ∗
            (l at_union{ul}ₗ n ◁ₗ{β} ty2 y) ∗ T y)
    ⊢ subsume (l ◁ₗ{β} active_union ul n ty1) (λ y : B, l ◁ₗ{β} variant ti (x y) (ty2 y)) T.
  Proof.
    iIntros "HT". iDestruct 1 as (ly Hly) "Hu".
    iDestruct (padded_focus with "Hu") as "[Hl Hpad]".
    rewrite /GetMemberUnionLoc/=. iDestruct ("HT" with "[$]") as (? <- <-) "[??]".
    iDestruct ("Hpad" with "[$]") as "?". iExists _. iFrame.
    move: Hly => /layout_of_member_ti_member ->. done.
  Qed.
  Definition subsume_active_union_variant_inst := [instance subsume_active_union_variant].
  Global Existing Instance subsume_active_union_variant_inst.

  Lemma subsume_variant_variant B ti x1 x2 l β ty1 ty2 T:
    (l at_union{ti.(ti_union_layout)}ₗ (ti_member ti x1).1 ◁ₗ{β} ty1 -∗
      ∃ y, ⌜ti.(ti_tag) x1 = ti.(ti_tag) (x2 y)⌝ ∗
      l at_union{ti.(ti_union_layout)}ₗ (ti_member ti x1).1 ◁ₗ{β} (ty2 y) ∗ T y)
    ⊢ subsume (l ◁ₗ{β} variant ti x1 ty1) (λ y : B, l ◁ₗ{β} variant ti (x2 y) (ty2 y)) T.
  Proof.
    iIntros "HT". rewrite !/(ty_own (variant _ _ _))/=/ti_member.
    iIntros "Hpad". iDestruct (padded_focus with "Hpad") as "[Hl Hpad]".
    iDestruct ("HT" with "Hl") as (? Heq) "[??]". iExists _. iFrame.
    rewrite Heq. by iApply "Hpad".
  Qed.
  Definition subsume_variant_variant_inst := [instance subsume_variant_variant].
  Global Existing Instance subsume_variant_variant_inst.

(*  Lemma type_place_variant K β ul n l ty ti x {Heq: TCEq (ti_member ti x).1 n} T :
    ⌜ul = ti.(ti_union_layout)⌝ ∗
     typed_place K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, variant ti x (typ t)))
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l β (variant ti x ty) T.
  Proof.
    move: Heq => /TCEq_eq <-.
    iIntros "[-> HP]" (Φ) "Hs HΦ" => /=.
    rewrite {2}/variant /padded/=. iDestruct "Hs" as (??) "[Hb [Hty Hpad]]".
    iApply (wp_get_member_union with "[#//]"). 1: by apply val_to_of_loc.
    iExists _. iSplit => //.
    iApply ("HP" with "[Hty]"). 1: by rewrite /GetMemberUnionLoc.
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    rewrite /variant/padded/GetMemberUnionLoc/=. iSplit => //. by iFrame.
  Qed.
  Definition type_place_variant_inst := [instance type_place_variant].
  Global Existing Instance type_place_variant_inst | 20.

  Lemma type_place_variant_neq K ul n l ty ti x T :
    (⌜ul = ti.(ti_union_layout)⌝ ∗ ⌜ty.(ty_has_op_type) (UntypedOp (ti_member ti x).2) MCNone⌝ ∗ ∀ v, v ◁ᵥ ty -∗ typed_place (GetMemberUnionPCtx ul n :: K) l Own (uninit ul) T)
    ⊢ typed_place (GetMemberUnionPCtx ul n :: K) l Own (variant ti x ty) T.
  Proof.
    iIntros "[-> [% HP]]". iApply (typed_place_subsume _ _ _ (uninit (ti_union_layout ti))).
    iApply subsume_padded_uninit. iSplit; [done|]. iIntros (v) "Hv $". iExists tt.
    by iApply "HP".
  Qed.
  Definition type_place_variant_neq_inst := [instance type_place_variant_neq].
  Global Existing Instance type_place_variant_neq_inst | 50. *)
End union.

Section tunion.
  Context `{!typeG OK_ty Σ} {cs : compspecs} {A : Type}.
  (*** tunion *)
  (* TODO: extract the inner type to a separate definition and make it typeclasses opaque. *)
  Program Definition tunion (ti : tunion_info A) : rtype A := {|
    rty r := {|
      ty_has_op_type :=
        is_struct_ot ti.(ti_base_layout) [tunion_tag ti r; variant ti r (ti.(ti_type) r)];
      ty_own β l := l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti r;
         variant ti r (ti.(ti_type) r)
      ];
      ty_own_val v := ty_own_val (struct ti.(ti_base_layout) [
         tunion_tag ti r;
         variant ti r (ti.(ti_type) r)
   ]) v;
   |}%I |}.
  Next Obligation. iIntros (?????). by apply ty_share. Qed.
  Next Obligation. iIntros (??????) "Hl". by iApply (ty_aligned with "Hl"). Qed.
  Next Obligation. iIntros (??????) "Hv". by iApply (ty_size_eq with "Hv"). Qed.
  Next Obligation. iIntros (??????) "Hl". by iApply (ty_deref with "Hl"). Qed.
  Next Obligation. iIntros (????????) "Hl Hv". by iApply (ty_ref with "[] Hl Hv"). Qed.
  Next Obligation. move => ???????. by apply ty_memcast_compat. Qed.

  Lemma simplify_hyp_tunion ti x l β T:
    (l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ] -∗ T)
    ⊢ simplify_hyp (l◁ₗ{β} x @ tunion ti) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simplify_hyp_tunion_inst := [instance simplify_hyp_tunion with 0%N].
  Global Existing Instance simplify_hyp_tunion_inst.

  Lemma simplify_goal_tunion ti x l β T:
    l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ] ∗ T
    ⊢ simplify_goal (l◁ₗ{β} x @ tunion ti) T.
  Proof. iIntros "[$ $]". Qed.
  Definition simplify_goal_tunion_inst := [instance simplify_goal_tunion with 0%N].
  Global Existing Instance simplify_goal_tunion_inst.

End tunion.

Global Typeclasses Opaque active_union variant tunion tunion_tag.
