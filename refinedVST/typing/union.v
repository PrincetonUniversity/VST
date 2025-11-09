Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs bytes (*padded*) struct int.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.
Require Import Coq.Program.Equality.

Definition GetMemberUnionLoc (l : address) (i : ident) (m : ident) : address := (l).
Notation "l 'at_union{' ul '}ₗ' m" := (GetMemberUnionLoc l ul m) (at level 10, format "l  'at_union{' ul '}ₗ'  m") : stdpp_scope.
Global Typeclasses Opaque GetMemberUnionLoc.
Arguments GetMemberUnionLoc : simpl never.

Section union.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (*** active_union *)
  Program Definition active_union (i : ident) (f : ident) (ty : type) : type := {|
    ty_own β l := ∃ m, <affine> ⌜∃ ul, (cenv_cs !! i)%maps = Some ul ∧ in_members f ul.(co_members) ∧ get_member f ul.(co_members) = m⌝ ∗
      <affine> ⌜l `has_layout_loc` Tunion i noattr⌝ ∗
      heap_withspacer β (sizeof (field_type (name_member m) (get_co i).(co_members))) (co_sizeof (get_co i))
        (λ p, match val2adr p with Some l => l ◁ₗ{β} ty | _ => False end) l;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ _ := True;
  |}%I.
  Solve Obligations with try done.
  Next Obligation.
    iIntros (ul f ty l E ?). iDestruct 1 as (ly ?) "($ & Hp)". iExists _. iSplitR => //.
    iDestruct "Hp" as "(H & ?)"; iSplitL "H"; first by iApply ty_share.
    rewrite /heap_spacer /mapsto_memory_block.at_offset. if_tac; first done.
    iApply inv_alloc. iModIntro. iExists _. iFrame; auto.
  Qed.

  Lemma has_layout_union_noattr : forall i a l, l `has_layout_loc` (Tunion i a) ↔ l `has_layout_loc` (Tunion i noattr).
  Proof.
    intros; rewrite /has_layout_loc /field_compatible; do 3 f_equiv; last f_equiv; try done.
    rewrite /align_compatible_dec.align_compatible /=.
    split; inversion 1; try done; eapply align_compatible_rec_Tunion; done.
  Qed.

  Lemma mapsto_union : forall id a l v, l ↦|Tunion id a| v ⊣⊢ aggregate_pred.union_pred (co_members (get_co id))
    (fun it v => mapsto_memory_block.withspacer Tsh (sizeof (field_type (name_member it) (co_members (get_co id))))
                        (co_sizeof (get_co id))
                        (data_at_rec Tsh (field_type (name_member it) (co_members (get_co id))) v))
    (unfold_reptype v) l.
  Proof.
    intros; rewrite /mapsto data_at_rec_eq //.
  Qed.

  #[local] Transparent field_type.

  Lemma type_place_uninit_union ge K (*β*) ul a n l T:
    (∃ ly, <affine> ⌜Ctypes.field_type n (co_members (get_co ul)) = Errors.OK ly⌝ ∗
    typed_place ge (GetMemberUnionPCtx ul n :: K) l Own (active_union ul n (uninit ly)) T)
    ⊢ typed_place ge (GetMemberUnionPCtx ul n :: K) l Own (uninit (Tunion ul a)) T.
  Proof.
    iDestruct 1 as (ly Hly) "HP".
    iIntros (Φ) "Hs HΦ" => /=.
    iApply ("HP" with "[Hs] HΦ").
    iApply (embed_mono with "Hs"); iIntros "Hs".
    pose proof (field_type_in_members n (co_members (get_co ul))) as Hin; rewrite Hly in Hin.
    iExists (get_member n (co_members (get_co ul))). iSplit => //.
    { iPureIntro. unfold get_co in *; destruct (cenv_cs !! ul)%maps eqn: Hi; try done.
      eauto. }
    rewrite uninit_memory_block // has_layout_union_noattr.
    iDestruct "Hs" as (?) "Hs"; iSplit => //=.
    rewrite name_member_get Hly.
    replace (match (cenv_cs !! ul)%maps with | Some co => co_sizeof co | None => 0 end) with (co_sizeof (get_co ul));
      last by rewrite /get_co; destruct (cenv_cs !! ul)%maps.
    rewrite -{1}(isptr_offset_val_zero l) // -withspacer_uninit_memory_block //.
    - iStopProof; f_equiv; try done.
      rewrite /mapsto_memory_block.at_offset; extensionality p.
      destruct p; try done.
      rewrite isptr_offset_val_zero //.
    - admit. (* volatile *)
    - apply (field_compatible_app_inv' [UnionField n]), field_compatible_nested_field in H; last done.
      rewrite app_nil_r /nested_field_type /nested_field_offset /= in H.
      apply compute_in_members_true_iff in Hin; rewrite Hin Hly // in H.
    - split.
      + replace ly with (field_type n (co_members (get_co ul))) by rewrite /= Hly //.
        etrans; first by apply sizeof_union_in_members.
        eapply sizeof_Tunion_co_sizeof, H.
      + destruct H as (_ & _ & Hsz & _); simpl in Hsz.
        replace (match (cenv_cs !! ul)%maps with | Some co => co_sizeof co | None => 0 end) with (co_sizeof (get_co ul)) in *;
          last by rewrite /get_co; destruct (cenv_cs !! ul)%maps.
        rep_lia.
    - destruct H as (_ & _ & Hsz & _); simpl in Hsz.
      replace (match (cenv_cs !! ul)%maps with | Some co => co_sizeof co | None => 0 end) with (co_sizeof (get_co ul)) in Hsz;
        last by rewrite /get_co; destruct (cenv_cs !! ul)%maps.
      lia.
  Admitted.
  Definition type_place_uninit_union_inst := [instance type_place_uninit_union].
  Global Existing Instance type_place_uninit_union_inst.

  Lemma type_place_active_union ge K β ul n l ty T:
    typed_place ge K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, active_union ul n (typ t)))
    ⊢ typed_place ge (GetMemberUnionPCtx ul n :: K) l β (active_union ul n ty) T.
  Proof.
    iIntros "HP" (Φ) "Hs HΦ !>" => /=.
    iDestruct "Hs" as (? (i & Hi & Hn & <-) ?) "[Hty Hspace]".
    iExists _, _. iSplit => //.
    { iPureIntro; split; first done.
      apply plain_members_union_field_offset; try done.
      destruct H as (_ & H & _). apply nested_pred_lemmas.complete_Tunion_plain in H.
      rewrite /get_co Hi // in H. }
    rewrite Ptrofs.add_zero /GetMemberUnionLoc; destruct l.
    iApply ("HP" with "Hty").
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    iExists _. rewrite /get_co Hi. iSplitR; first by eauto.
    by iFrame.
  Qed.
  Definition type_place_active_union_inst := [instance type_place_active_union].
  Global Existing Instance type_place_active_union_inst.

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

  Lemma index_of_ti_member ti (x : A):
    (get_co (ti_union_layout ti)).(co_members) !! (ti.(ti_tag) x) = Some (ti_member ti x).
  Proof.
    rewrite /ti_member.
    destruct (ti_tags_valid ti x) as [? Heq]. rewrite Heq //.
  Qed.

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

  Global Instance tunion_tag_defined ti x : DefinedTy size_t (tunion_tag ti x).
  Proof.
    iIntros (?) "H"; rewrite /tunion_tag; simpl_type.
    iApply (defined_ty with "H").
  Qed.

  Lemma subsume_int_tunion_tag B ti x (n : Z) l β T:
    (∃ y, <affine> ⌜ti.(ti_tag) (x y) =@{Z} n⌝ ∗ T y)
    ⊢ subsume (l ◁ₗ{β} n @ int size_t) (λ y : B, l ◁ₗ{β} tunion_tag ti (x y)) T.
  Proof. iIntros "[% [<- ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_int_tunion_tag_inst := [instance subsume_int_tunion_tag].
  Global Existing Instance subsume_int_tunion_tag_inst.

  Lemma subsume_int_tunion_tag' B ti x (n : Z) l β (T : B → assert):
    (∃ y, <affine> ⌜ti.(ti_tag) (x y) =@{Z} n⌝ ∗ T y)
    ⊢ subsume ⎡l ◁ₗ{β} n @ int size_t⎤ (λ y : B, ⎡l ◁ₗ{β} tunion_tag ti (x y)⎤) T.
  Proof. iIntros "[% [<- ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_int_tunion_tag'_inst := [instance subsume_int_tunion_tag'].
  Global Existing Instance subsume_int_tunion_tag'_inst.

  Lemma subsume_tunion_tag B ti x1 x2 l β T:
    (∃ y, <affine> ⌜ti.(ti_tag) x1 = ti.(ti_tag) (x2 y)⌝ ∗ T y)
    ⊢ subsume (l ◁ₗ{β} tunion_tag ti x1) (λ y : B, l ◁ₗ{β} tunion_tag ti (x2 y)) T.
  Proof. rewrite /ty_own/=. iIntros "[% [-> ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_tunion_tag_inst := [instance subsume_tunion_tag].
  Global Existing Instance subsume_tunion_tag_inst.

  Lemma subsume_tunion_tag' B ti x1 x2 l β (T : B → assert):
    (∃ y, <affine> ⌜ti.(ti_tag) x1 = ti.(ti_tag) (x2 y)⌝ ∗ T y)
    ⊢ subsume ⎡l ◁ₗ{β} tunion_tag ti x1⎤ (λ y : B, ⎡l ◁ₗ{β} tunion_tag ti (x2 y)⎤) T.
  Proof. rewrite /ty_own/=. iIntros "[% [-> ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_tunion_tag'_inst := [instance subsume_tunion_tag'].
  Global Existing Instance subsume_tunion_tag'_inst.

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

  Opaque field_type.

  (* up *)
  Lemma union_Prop_cons2:
    forall it it' m (A: member -> Type)
     (P: forall it, A it -> Prop)
     (v: compact_sum (map A (it::it'::m))),
   aggregate_pred.aggregate_pred.union_Prop (it :: it' :: m) P v =
     match v with inl v => P _ v | inr v => aggregate_pred.aggregate_pred.union_Prop (it'::m) P v end.
  Proof.
    intros.
    destruct v; reflexivity.
  Qed.

  Lemma union_pred_irrel : forall m {A} (P : forall it, A it -> val -> mpred) v p p',
    (forall it v, P it v p = P it v p') -> aggregate_pred.union_pred m P v p = aggregate_pred.union_pred m P v p'.
  Proof.
    induction m; intros; first done.
    destruct m.
    - simpl; auto.
    - setoid_rewrite union_pred_cons2.
      destruct v; auto.
  Qed.

  (* up? *)
  Definition inject_field mems0 mems n m (Hindex : mems !! n = Some m)
    (v : reptype (field_type (name_member m) mems0)) : compact_sum (map (λ it : member, reptype (field_type (name_member it) mems0)) mems).
  Proof.
    generalize dependent n; induction mems; intros.
    { exact tt. }
    destruct mems.
    - destruct n; inv Hindex.
      exact v.
    - destruct n.
      + inv Hindex; exact (inl v).
      + exact (inr (IHmems _ Hindex)).
  Defined.

  Lemma inject_field_cons2 : forall mems0 m0 m1 mems n m (Hindex : (m0 :: m1 :: mems) !! S n = Some m)
    (v : reptype (field_type (name_member m) mems0)), inject_field mems0 (m0 :: m1 :: mems) (S n) m Hindex v =
    inr (inject_field mems0 (m1 :: mems) n m Hindex v).
  Proof. reflexivity. Qed.

  Lemma inject_field_union_pred : forall mems0 P mems n m (Hindex : mems !! n = Some m) v p,
    aggregate_pred.union_pred mems P (inject_field mems0 mems n m Hindex v) p = P m v p.
  Proof.
    induction mems; first done; intros.
    destruct mems.
    - destruct n; dependent destruction Hindex; done.
    - destruct n.
      + dependent destruction Hindex; done.
      + fold aggregate_pred.aggregate_pred.union_pred; rewrite inject_field_cons2 union_pred_cons2 //.
  Qed.

  Lemma inject_field_union_Prop : forall mems0 P mems n m (Hindex : mems !! n = Some m) v,
    aggregate_pred.union_Prop mems P (inject_field mems0 mems n m Hindex v) = P m v.
  Proof.
    induction mems; first done; intros.
    destruct mems.
    - destruct n; dependent destruction Hindex; done.
    - destruct n.
      + dependent destruction Hindex; done.
      + fold aggregate_pred.aggregate_pred.union_Prop; rewrite inject_field_cons2 union_Prop_cons2 //.
  Qed.

  Definition inject_ti_field ti x v := inject_field (get_co ti.(ti_union_layout)).(co_members)
    _ _ _ (index_of_ti_member ti x) v.

  Import EqNotations.

  (*** variant *)
  Program Definition variant (ti : tunion_info A) (x : A) (ty : type) : type := {|
    ty_has_op_type ot mt := (∃ a, ot = Tunion ti.(ti_union_layout) a) /\ ty.(ty_has_op_type) (field_type (name_member (ti_member ti x)) (get_co ti.(ti_union_layout)).(co_members)) MCNone;
    ty_own β l := (<affine> ⌜l `has_layout_loc` Tunion ti.(ti_union_layout) noattr⌝ ∗ heap_withspacer β (sizeof (field_type (name_member (ti_member ti x)) (get_co ti.(ti_union_layout)).(co_members))) (co_sizeof (get_co ti.(ti_union_layout)))
      (λ p, match val2adr p with Some l => l ◁ₗ{β} ty | _ => False end) l)%I;
    ty_own_val cty v := (∃ v', <affine> ⌜v `has_layout_val` cty ∧
      ∃ a (Hcty : cty = Tunion ti.(ti_union_layout) a), unfold_reptype (rew Hcty in v) = inject_ti_field ti x v'⌝ ∗
      v' ◁ᵥ|field_type (name_member (ti_member ti x)) (get_co ti.(ti_union_layout)).(co_members)| ty)%I;
  |}.
  Next Obligation. iIntros (??????) "($ & H & ?)". iSplitL "H"; first by iApply ty_share.
    rewrite /heap_spacer /mapsto_memory_block.at_offset. if_tac; first done.
    iApply inv_alloc. iModIntro. iExists _. iFrame; auto.
  Qed.
  Next Obligation. iIntros (?????? ((? & ->) & ?)) "(% & Hv & _)".
    rewrite has_layout_union_noattr //.
  Qed.
  Next Obligation. iIntros (?????? ((? & ->) & ?)) "(% & ($ & %) & Hv)". Qed.
  Next Obligation. iIntros (?????? ((? & ->) & ?)) => /=.
    iIntros "(_ & Hl & Hspacer)".
    iDestruct (ty_deref with "Hl") as (v) "(? & Hv)"; first done.
    rewrite /has_layout_val /type_is_volatile. setoid_rewrite value_fits_eq; simpl.
    setoid_rewrite mapsto_union.
    iExists (fold_reptype(t := Tunion _ _) (inject_ti_field ti x v)).
    iDestruct (ty_size_eq with "Hv") as %(? & _); first done.
    rewrite unfold_fold_reptype inject_field_union_pred -heap_withspacer_eq; iFrame.
    iPureIntro.
    split; first by rewrite /aggregate_pred.aggregate_pred.union_Prop inject_field_union_Prop.
    exists _, eq_refl; rewrite /= unfold_fold_reptype //.
  Qed.
  Next Obligation. iIntros (??????? ((? & ->) & ?) Hly) "Hl Hv" => /=.
    rewrite mapsto_union.
    iDestruct "Hv" as "(% & (% & % & % & %Hinj) & Hv)".
    iSplit; first by erewrite <- has_layout_union_noattr.
    dependent destruction Hcty; simpl in *.
    rewrite Hinj inject_field_union_pred -heap_withspacer_eq.
    iDestruct "Hl" as "(Hl & $)"; simpl.
    destruct l; iApply (ty_ref with "[%] Hl Hv"); try done.
    pose proof (index_of_ti_member ti x) as Hf.
    apply elem_of_list_lookup_2, elem_of_list_In in Hf.
    apply (in_map name_member) in Hf.
    apply (field_compatible_app_inv' [UnionField (name_member (ti_member ti x))]), field_compatible_nested_field in Hly; last done.
    rewrite app_nil_r /nested_field_type /nested_field_offset /= in Hly.
    apply compute_in_members_true_iff in Hf; rewrite Hf Ptrofs.add_zero // in Hly.
  Qed.
  (* Next Obligation. iIntros (????????) "Hv". by iApply (ty_memcast_compat with "Hv"). Qed. *)

  Lemma subsume_active_union_variant B ti i x l β ty1 ty2 n T:
    (l at_union{i}ₗ n ◁ₗ{β} ty1 -∗
      ∃ y, <affine> ⌜ti.(ti_union_layout) = i⌝ ∗ <affine> ⌜name_member (ti_member ti (x y)) = n⌝ ∗
            (l at_union{i}ₗ n ◁ₗ{β} ty2 y) ∗ T y)
    ⊢ subsume (l ◁ₗ{β} active_union i n ty1) (λ y : B, l ◁ₗ{β} variant ti (x y) (ty2 y)) T.
  Proof.
    iIntros "HT". iDestruct 1 as (? (? & ? & ? & <-) ?) "[Hl Hpad]".
    rewrite /GetMemberUnionLoc/=. destruct l; iDestruct ("HT" with "[$]") as (? <- <-) "[??]".
    rewrite name_member_get. iExists _. iFrame. done.
  Qed.
  Definition subsume_active_union_variant_inst := [instance subsume_active_union_variant].
  Global Existing Instance subsume_active_union_variant_inst.

  Lemma subsume_active_union_variant' B ti i x l β ty1 ty2 n (T : B → assert):
    (⎡l at_union{i}ₗ n ◁ₗ{β} ty1⎤ -∗
      ∃ y, <affine> ⌜ti.(ti_union_layout) = i⌝ ∗ <affine> ⌜name_member (ti_member ti (x y)) = n⌝ ∗
            ⎡l at_union{i}ₗ n ◁ₗ{β} ty2 y⎤ ∗ T y)
    ⊢ subsume ⎡l ◁ₗ{β} active_union i n ty1⎤ (λ y : B, ⎡l ◁ₗ{β} variant ti (x y) (ty2 y)⎤) T.
  Proof.
    iIntros "HT". iDestruct 1 as (? (? & ? & ? & <-) ?) "[Hl Hpad]".
    rewrite /GetMemberUnionLoc/=. destruct l; iDestruct ("HT" with "[$]") as (? <- <-) "[??]".
    rewrite name_member_get. iExists _. iFrame. done.
  Qed.
  Definition subsume_active_union_variant'_inst := [instance subsume_active_union_variant'].
  Global Existing Instance subsume_active_union_variant'_inst.

  Lemma subsume_variant_variant' B ti x1 x2 l β ty1 ty2 (T : B → assert):
    (⎡l at_union{ti.(ti_union_layout)}ₗ (name_member (ti_member ti x1)) ◁ₗ{β} ty1⎤ -∗
      ∃ y, <affine> ⌜ti.(ti_tag) x1 = ti.(ti_tag) (x2 y)⌝ ∗
      ⎡l at_union{ti.(ti_union_layout)}ₗ (name_member (ti_member ti x1)) ◁ₗ{β} (ty2 y)⎤ ∗ T y)
    ⊢ subsume ⎡l ◁ₗ{β} variant ti x1 ty1⎤ (λ y : B, ⎡l ◁ₗ{β} variant ti (x2 y) (ty2 y)⎤) T.
  Proof.
    iIntros "HT". rewrite {3 4}/ty_own/GetMemberUnionLoc/=/ti_member.
    iIntros "(% & Hl & Hpad)".
    destruct l; iDestruct ("HT" with "Hl") as (? Heq) "[??]". iExists _. iFrame.
    rewrite Heq. iFrame. done.
  Qed.
  Definition subsume_variant_variant'_inst := [instance subsume_variant_variant'].
  Global Existing Instance subsume_variant_variant'_inst.

  Lemma type_place_variant ge K β ul n l ty ti x {Heq: TCEq (name_member (ti_member ti x)) n} T :
    <affine> ⌜ul = ti.(ti_union_layout)⌝ ∗
     typed_place ge K (l at_union{ul}ₗ n) β ty (λ l2 β ty2 typ, T l2 β ty2 (λ t, variant ti x (typ t)))
    ⊢ typed_place ge (GetMemberUnionPCtx ul n :: K) l β (variant ti x ty) T.
  Proof.
    move: Heq => /TCEq_eq <-.
    iIntros "[-> HP]" (Φ) "Hs HΦ !>" => /=.
    rewrite {1}/ty_own /=. iDestruct "Hs" as (?) "[Hty Hpad]".
    pose proof (index_of_ti_member ti x) as Hf.
    unfold get_co in *; destruct (cenv_cs !! ti_union_layout ti)%maps eqn: Hi; last done.
    apply elem_of_list_lookup_2, elem_of_list_In in Hf.
    apply (in_map name_member) in Hf.
    iExists _, _. iSplit => //.
    { iPureIntro; split; first done.
      apply plain_members_union_field_offset; try done.
      destruct H as (_ & H & _). apply nested_pred_lemmas.complete_Tunion_plain in H.
      rewrite /get_co Hi // in H. }
    rewrite Ptrofs.add_zero /GetMemberUnionLoc; destruct l.
    iApply ("HP" with "Hty").
    iIntros (l2 β2 ty2 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [-HT] HT").
    iIntros (ty') "Hty". iMod ("Hc" with "Hty") as "[Hty $]". iModIntro.
    iFrame.
    rewrite /get_co Hi. iSplitR; eauto.
  Qed.
  Definition type_place_variant_inst := [instance type_place_variant].
  Global Existing Instance type_place_variant_inst | 20.

  Lemma type_place_variant_neq ge K ul n l ty ti x T :
    (<affine> ⌜ul = ti.(ti_union_layout)⌝ ∗ <affine> ⌜ty.(ty_has_op_type) (field_type (name_member (ti_member ti x)) (get_co ul).(co_members)) MCNone⌝ ∗
     ∀ v, ⎡v ◁ᵥ|field_type (name_member (ti_member ti x)) (get_co ul).(co_members)|  ty⎤ -∗ typed_place ge (GetMemberUnionPCtx ul n :: K) l Own (uninit (Tunion ul noattr)) T)
    ⊢ typed_place ge (GetMemberUnionPCtx ul n :: K) l Own (variant ti x ty) T.
  Proof.
    iIntros "[-> [% HP]]". iApply (typed_place_subsume _ _ _ _ (uninit (Tunion (ti_union_layout ti) noattr))).
    iApply uninit_mono'.
    { split; eauto. }
    iIntros (?) "(% & % & Hv)".
    iExists tt. by iApply "HP".
  Qed.
  Definition type_place_variant_neq_inst := [instance type_place_variant_neq].
  Global Existing Instance type_place_variant_neq_inst | 50.
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
  (* Next Obligation. move => ???????. by apply ty_memcast_compat. Qed. *)

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

  Lemma simplify_hyp_tunion' ti x l β (T : assert):
    (⎡l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ]⎤ -∗ T)
    ⊢ simplify_hyp ⎡l◁ₗ{β} x @ tunion ti⎤ T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simplify_hyp_tunion'_inst := [instance simplify_hyp_tunion' with 0%N].
  Global Existing Instance simplify_hyp_tunion'_inst.

  Lemma simplify_goal_tunion' ti x l β (T : assert):
    ⎡l ◁ₗ{β} struct ti.(ti_base_layout) [
         tunion_tag ti x;
         variant ti x (ti.(ti_type) x) ]⎤ ∗ T
    ⊢ simplify_goal ⎡l◁ₗ{β} x @ tunion ti⎤ T.
  Proof. iIntros "[$ $]". Qed.
  Definition simplify_goal_tunion'_inst := [instance simplify_goal_tunion' with 0%N].
  Global Existing Instance simplify_goal_tunion'_inst.

End tunion.

Global Typeclasses Opaque active_union variant tunion tunion_tag.
