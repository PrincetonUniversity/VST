From VST.typing Require Export type.
From VST.typing Require Import programs boolean int.
From VST.typing Require Import type_options.

(** We need to use this unbundled approach to ensure that ROptionable
uses the same instances as Optionable.
  TODO: findout if there is a better way, maybe using Canonical Structures?
 *)

Class Optionable `{!typeG OK_ty Σ} {cs : compspecs} (cty : Ctypes.type) (ty : type) (optty : type) (ot1 ot2 : Ctypes.type) := {
  opt_pre : val → val → iProp Σ;
  opt_bin_op (bty beq : bool) v1 v2 σ v :
    (⊢ opt_pre v1 v2 -∗ (if bty then v1 ◁ᵥₐₗ|cty| ty else v1 ◁ᵥₐₗ|cty| optty) -∗ v2 ◁ᵥₐₗ|cty| optty -∗ juicy_mem.mem_auth σ -∗
      ⌜sem_binary_operation _ (if beq then Cop.Oeq else Cop.One) v1 ot1 v2 ot2 σ = Some v ↔ Vint (Int.repr (bool_to_Z (xorb bty beq))) = v⌝);
}.
Arguments opt_pre {_ _ _ _ _} _ {_ _ _ _} _ _.

Class OptionableAgree `{!typeG OK_ty Σ} {cs : compspecs} (ty1 ty2 : type) : Prop :=
  optionable_dist : True.

Section optional.
  Context `{!typeG OK_ty Σ} {cs : compspecs} (ge : genv).
  Check opt_pre .
  
  Check Optionable.

  Global Program Instance optionable_ty_of_rty A (r : rtype A) `{!Inhabited A} optty ot1 ot2
    `{!∀ x, Optionable cty (x @ r) optty ot1 ot2}: Optionable cty r optty ot1 ot2 := {|
     opt_pre (v1 v2 : val) := (∀ x, opt_pre (x @ r) v1 v2)%I
  |}.
  Next Obligation.
    iIntros(A r?????? bty beq v1 v2 σ v) "Hpre Hv1 Hv2".
    unfold ty_of_rty; simpl_type.
    destruct bty. 1: iDestruct "Hv1" as (y) "Hv1".
    all: iApply (opt_bin_op with "Hpre [Hv1] Hv2") => /= //.
    Unshelve.
    apply inhabitant.
  Qed.

  Global Instance optionable_agree_wr1 A (ty1 : rtype A) p ty2 `{!OptionableAgree ty1 ty2} : OptionableAgree (p @ ty1) ty2.
  Proof. done. Qed.
  Global Instance optionable_agree_wr2 A (ty2 : rtype A) p ty1 `{!OptionableAgree ty1 ty2} : OptionableAgree ty1 (p @ ty2).
  Proof. done. Qed.
  Global Instance optionable_agree_id ty : OptionableAgree ty ty.
  Proof. done. Qed.

  Check tptr.
  
  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition optional_type  (ty : type) (optty : type) (b : Prop) : type := {|
      ty_has_op_type ot mt := (ty.(ty_has_op_type) ot mt ∧ optty.(ty_has_op_type) ot mt)%type;
      ty_own β l := (<affine> ⌜b⌝ ∗ l◁ₗ{β}ty ∨ <affine> ⌜¬b⌝ ∗ l◁ₗ{β}optty)%I;
                                                                                 ty_own_val cty v := (<affine> ⌜b⌝ ∗ v ◁ᵥ|cty| ty ∨ <affine> ⌜¬b⌝ ∗ v ◁ᵥ|cty| optty)%I
  |}.
  Next Obligation.
    iIntros (??????).
    by iDestruct 1 as "[[% H]|[% H]]";iMod (ty_share with "H") => //; iModIntro; [iLeft | iRight ]; iFrame.
  Qed.
  Next Obligation.
    iIntros (ty?????[??]). by iDestruct 1 as "[[% Hv]|[% Hv]]";iDestruct (ty_aligned with "Hv") as %?.
  Qed.
  Next Obligation.
    iIntros (ty?????[??]).
    iDestruct 1 as "[[% Hv]|[% Hv]]";iDestruct (ty_size_eq with "Hv") as %?; eauto.
  Qed.
  Next Obligation.
    iIntros (ty optty ????[??]) "Hl".
    iDestruct "Hl" as "[[% Hl]|[% Hl]]"; iDestruct (ty_deref with "Hl") as (?) "[? ?]"; eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (ty optty ?????[??]?) "Hl Hv".
    iDestruct "Hv" as "[[% Hv]|[% Hv]]"; iDestruct (ty_ref with "[] Hl Hv") as "H"; rewrite -?opt_alt_sz//;
       [iLeft | iRight]; by iFrame.
  Qed.
(*  Next Obligation.
    iIntros (ty optty b v ot mt st [??]) "[[% Hv]|[% Hv]]".
    all: iDestruct (ty_memcast_compat with "Hv") as "Hv" => //.
    all: case_match => //. 1: iLeft. 2: iRight.
    all: by iFrame.
  Qed. *)

  Global Instance optional_type_le : Proper ((⊑) ==> (⊑) ==> (=) ==> (⊑)) optional_type.
  Proof. solve_type_proper. Qed.
  Global Instance optional_type_proper : Proper ((≡) ==> (≡) ==> (=) ==> (≡)) optional_type.
  Proof. solve_type_proper. Qed.

  (* Never use optional without the refinement! This will fail
  horribly since the implicit refinement might not be decidable! Use
  optionalO with () instead. *)
  Definition optional (ty : type) (optty : type) : rtype _ := RType (optional_type ty optty).

(*   Global Instance optional_loc_in_bounds ty e ot β n `{!LocInBounds ty β n} `{!LocInBounds ot β n}:
    LocInBounds (e @ optional ty ot) β n.
  Proof.
    constructor. rewrite /with_refinement /=. iIntros (l) "Hl".
    iDestruct "Hl" as "[[_ Hl]|[_ Hl]]"; by iApply (loc_in_bounds_in_bounds with "Hl").
  Qed.
 *)
  (* We could add rules like *)
  (* Lemma simplify_optional_goal ty optty l β T b `{!Decision b}: *)
  (*   T (if decide b then l◁ₗ{β}ty else l◁ₗ{β}optty) -∗ *)
  (*   simplify_goal (l◁ₗ{β} b @ optional ty optty) T. *)
  (* but that would lead to the automation doing a case split out of
  despair which is not a good user experience. Thus you should make
  sure that the other rules in this file work for you, which don't
  cause unnecssary case splits. *)

  (* TODO: should be allow different opttys? *)
  Global Instance simple_subsume_place_optional ty1 ty2 optty b1 b2 `{!Affine P} `{!SimpleSubsumePlace ty1 ty2 P}:
    SimpleSubsumePlace (b1 @ optional ty1 optty) (b2 @ optional ty2 optty) (<affine> ⌜b1 ↔ b2⌝ ∗ P).
  Proof.
    iIntros (l β) "HP Hl". iDestruct "HP" as (Hequiv) "HP".
    iDestruct "Hl" as "[[% Hl]|[% Hl]]"; [iLeft | iRight]; rewrite -Hequiv. 2: by iFrame.
    iSplit => //. iApply (@simple_subsume_place with "HP Hl").
  Qed.

  Check SimpleSubsumeVal.

  Global Instance simple_subsume_val_optional ty1 ty2 optty b1 b2
       `{!Affine P} `{!SimpleSubsumeVal cty ty1 ty2 P}:
    SimpleSubsumeVal cty (b1 @ optional ty1 optty) (b2 @ optional ty2 optty) (<affine> ⌜b1 ↔ b2⌝ ∗ P).
  Proof.
    iIntros (v) "[Heq P] H". rewrite /ty_own_val /=.
    iDestruct "Heq" as "%Heq".
    apply PropExtensionality.propositional_extensionality in Heq.
    rewrite Heq.
    iDestruct "H" as "[[?H] | [??]]"; last (iRight; by iFrame).
    iLeft. iFrame. iApply (@simple_subsume_val with "P H").
  Qed.

  Lemma subsume_optional_optty_ref A b ty optty l β T:
    (∃ x, <affine> ⌜¬ (b x)⌝ ∗ T x) ⊢ subsume (l ◁ₗ{β} optty) (λ x : A, l ◁ₗ{β} (b x) @ optional (ty x) optty) T.
  Proof. iIntros "[% [Hb ?]] Hl". iExists _. iFrame. iRight. by iFrame. Qed.
  Definition subsume_optional_optty_ref_inst := [instance subsume_optional_optty_ref].
  Global Existing Instance subsume_optional_optty_ref_inst.

  Lemma subsume_optional_ty_ref A b (ty : A → type) ty' optty l β
    `{!∀ x, OptionableAgree (ty x) ty'} T:
    (l ◁ₗ{β} ty' -∗ ∃ x, l ◁ₗ{β} ty x ∗ <affine> ⌜b x⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} ty') (λ x : A, l ◁ₗ{β} (b x) @ optional (ty x) (optty x)) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (?) "[? [% ?]]".
    iExists _. iFrame. iLeft. by iFrame.
  Qed.
  Definition subsume_optional_ty_ref_inst := [instance subsume_optional_ty_ref].
  Global Existing Instance subsume_optional_ty_ref_inst.

  Lemma subsume_optional_val_optty_ref A b cty ty optty v T:
    (∃ x, <affine> ⌜¬ b x⌝ ∗ T x) ⊢ subsume (v ◁ᵥ|cty| optty) (λ x : A, v ◁ᵥ|cty| (b x) @ optional (ty x) optty) T.
  Proof. iIntros "[% [Hb ?]] Hl". iExists _. iFrame. iRight. by iFrame. Qed.
  Definition subsume_optional_val_optty_ref_inst := [instance subsume_optional_val_optty_ref].
  Global Existing Instance subsume_optional_val_optty_ref_inst.

  Lemma subsume_optional_val_ty_ref A b cty ty ty' optty v `{!∀ x, OptionableAgree (ty x) ty'} T:
    (v ◁ᵥ|cty| ty' -∗ ∃ x, v ◁ᵥ|cty| ty x ∗ <affine> ⌜b x⌝ ∗ T x)
      ⊢ subsume (v ◁ᵥ|cty| ty') (λ x : A, v ◁ᵥ|cty| (b x) @ optional (ty x) (optty x)) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (?) "[? [% ?]]".
    iExists _. iFrame. iLeft. by iFrame.
  Qed.
  Definition subsume_optional_val_ty_ref_inst := [instance subsume_optional_val_ty_ref].
  Global Existing Instance subsume_optional_val_ty_ref_inst.

  Inductive trace_optional :=
  | TraceOptionalEq (P : Prop)
  | TraceOptionalNe (P : Prop).

  Check opt_pre.
  
  Lemma type_eq_optional_refined v1 v2 (cty : Ctypes.type) (ty optty : type) (ot1 ot2 : Ctypes.type)
    `{!Optionable cty ty optty ot1 ot2}
    `{!Affine (v2 ◁ᵥₐₗ|cty| optty)} b (T : _ → _ → assert)
    (* We'll throw away any ownership associated with v2 (e.g. through an ownership type), so it needs to be affine.
       We could require T to be absorbing instead. *)  :
    ⎡opt_pre ty v1 v2⎤ ∧
    case_if b
      (li_trace (TraceOptionalEq b) (⎡v1 ◁ᵥₐₗ|cty| ty⎤ -∗ T (i2v (bool_to_Z false) tint) (false @ boolean tint)))
      (li_trace (TraceOptionalEq (¬ b)) (⎡v1 ◁ᵥₐₗ|cty| optty⎤ -∗ T (i2v (bool_to_Z true) tint) (true @ boolean tint)))
      ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|cty| b @ (optional ty optty)⎤ v2 ⎡v2 ◁ᵥₐₗ|cty| optty⎤ Oeq ot1 ot2 tint  T.
  Proof.
    iIntros "HT Hv1 Hv2" (Φ) "HΦ".
    iDestruct "Hv1" as "[[% Hv1]|[% Hv1]]".
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z false) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op true true with "Hpre Hv1 Hv2 Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      rewrite bi.and_elim_r.
      iDestruct "HT" as "[HT _]". iFrame.
      iSpecialize ("HΦ" $! (i2v (bool_to_Z false) _ ) (false @ boolean tint)).
      iApply ("HΦ" with "[]").
      { rewrite /ty_own_val_at /ty_own_val /=. iSplit; auto. by iExists _. }
      iApply ("HT" with "[] Hv1"); try done.
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z true) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op false true with "Hpre Hv1 Hv2 Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      iDestruct "HT" as "[_ [_ HT]]". iFrame.
      iDestruct ("HT" with "[//] Hv1") as "HT".
      iApply ("HΦ" with "[] HT").
      rewrite /ty_own_val_at /ty_own_val /=. iSplit; auto. by iExists _.
  Qed.
  Definition type_eq_optional_refined_inst := [instance type_eq_optional_refined].
  Global Existing Instance type_eq_optional_refined_inst.

  Lemma type_eq_optional_neq v1 v2 (cty : Ctypes.type) ty optty ot1 ot2
    `{!Optionable cty ty optty ot1 ot2} `{!Affine (v2 ◁ᵥₐₗ|cty| optty)} T :
    ⎡opt_pre ty v1 v2⎤ ∧ (∀ v, ⎡v1 ◁ᵥₐₗ|cty| ty⎤ -∗ T v (false @ boolean tint))
                           ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|cty| ty⎤ v2 ⎡v2 ◁ᵥₐₗ|cty| optty⎤ Oeq ot1 ot2 tint T.
  Proof.
    iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ".
    iIntros "!>" (?) "Hctx !>".
    iExists (i2v (bool_to_Z false) tint).
    iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op true true with "Hpre Hv1 Hv2 Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
    }
    iDestruct ("HT" with "Hv1") as "HT". iFrame.
    iApply "HΦ" => //.
    rewrite /ty_own_val_at /ty_own_val /=. iSplit; auto. by iExists _.
  Qed.
  Definition type_eq_optional_neq_inst := [instance type_eq_optional_neq].
  Global Existing Instance type_eq_optional_neq_inst.

  Lemma type_neq_optional v1 v2 (cty : Ctypes.type) ty optty ot1 ot2
    `{!Optionable cty ty optty ot1 ot2} `{!Affine (v2 ◁ᵥₐₗ|cty| optty)} b T :
    ⎡opt_pre ty v1 v2⎤ ∧
    case_if b
      (li_trace (TraceOptionalNe b) (⎡v1 ◁ᵥₐₗ|cty| ty⎤ -∗ T (i2v (bool_to_Z true) tint) (true @ boolean tint)))
      (li_trace (TraceOptionalNe (¬ b)) (⎡v1 ◁ᵥₐₗ|cty| optty⎤ -∗ T (i2v (bool_to_Z false) tint) (false @ boolean tint)))
      ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|cty| b @ (optional ty optty)⎤ v2 ⎡v2 ◁ᵥₐₗ|cty| optty⎤ Cop.One ot1 ot2 tint T.
  Proof.
    unfold li_trace. iIntros "HT Hv1 Hv2" (Φ) "HΦ".
    iDestruct "Hv1" as "[[% Hv1]|[% Hv1]]".
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z true) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op true false with "Hpre Hv1 Hv2 Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      iDestruct "HT" as "[_ [HT _]]". iFrame.
      iDestruct ("HT" with "[//] Hv1") as "HT".
      iApply ("HΦ" with "[] HT").
      rewrite /ty_own_val_at /ty_own_val /=. iSplit; auto. by iExists _.
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z false) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op false false with "Hpre Hv1 Hv2 Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      iDestruct "HT" as "[_ [_ HT]]". iFrame.
      iDestruct ("HT" with "[//] Hv1") as "HT".
      iApply ("HΦ" with "[] HT").
      rewrite /ty_own_val_at /ty_own_val /=. iSplit; auto. by iExists _.
  Qed.
  Definition type_neq_optional_inst := [instance type_neq_optional].
  Global Existing Instance type_neq_optional_inst.

  (*
  Global Program Instance optional_copyable b ty optty `{!Copyable ty} `{!Copyable optty} : Copyable (b @ optional ty optty).
  Next Obligation.
    iIntros (b ty optty ? ? E ly l ? [??]) "[[% Hl]|[% Hl]]".
    all: iMod (copy_shr_acc with "Hl") as (?? ?) "[?[??]]" => //.
    all: iModIntro; iSplit => //; rewrite /=?opt_alt_sz => //; iExists _, _; iFrame.
    - by iLeft; iFrame.
    - by iRight; iFrame.
  Qed.
  *)

End optional.
Global Typeclasses Opaque optional_type optional.
Notation "optional< ty , optty >" := (optional ty optty)
  (only printing, format "'optional<' ty ,  optty '>'") : printing_sugar.

Notation "'optional' == ... : P" := (TraceOptionalEq P) (at level 100, only printing).
Notation "'optional' != ... : P" := (TraceOptionalNe P) (at level 100, only printing).

Section optionalO.
  Context `{!typeG OK_ty Σ} {cs : compspecs} (ge: genv).
    (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition optionalO_type {A : Type} (cty : Ctypes.type) (ty : A → type) (optty : type) (b : option A) : type := {|
      ty_has_op_type ot mt := ((∀ x, (ty x).(ty_has_op_type) ot mt) ∧ optty.(ty_has_op_type) ot mt)%type;
      ty_own β l := (if b is Some x return _ then l◁ₗ{β}(ty x) else l◁ₗ{β}optty)%I;
      ty_own_val cty v := (if b is Some x return _ then v ◁ᵥ|cty| (ty x) else v ◁ᵥ|cty| optty)%I
  |}.
  Next Obligation.
    iIntros (A ty ??????). destruct b; by apply ty_share.
  Qed.
  Next Obligation.
    iIntros (A ty ??????(?&?)) "Hv".
    destruct b; iDestruct (ty_aligned with "Hv") as %Ha => //.
  Qed.
  Next Obligation.
    iIntros (A ty ??????(?&?)) "Hv".
    destruct b; iDestruct (ty_size_eq with "Hv") as %Ha => //.
  Qed.
  Next Obligation.
    iIntros (A ty optty?[]???[??]) "Hl"; rewrite /with_refinement/ty_own/=; iDestruct (ty_deref with "Hl") as (?) "[? ?]"; eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (A ty optty?[]????[??]?) "Hl Hv"; iApply (ty_ref with "[] Hl Hv") => //.
  Qed.
(*   Next Obligation.
    iIntros (A ty optty [x|] v ot mt st [??]) "Hl".
    all: by iDestruct (ty_memcast_compat with "Hl") as "Hl".
  Qed. *)

  Global Instance optionalO_type_le A cty:
    Proper (pointwise_relation A (⊑) ==> (⊑) ==> (eq) ==> (⊑)) (optionalO_type cty).
  Proof. solve_type_proper. Qed.
  Global Instance optionalO_type_proper A cty:
    Proper (pointwise_relation A (≡) ==> (≡) ==> (eq) ==> (≡)) (optionalO_type cty).
  Proof. solve_type_proper. Qed.

  Definition optionalO {A : Type} cty (ty : A → type) (optty : type) : rtype _ :=
    RType (optionalO_type cty ty optty).

(*   Global Instance optionalO_loc_in_bounds A (ty : A → type) e ot β n `{!∀ x, LocInBounds (ty x) β n} `{!LocInBounds ot β n}:
    LocInBounds (e @ optionalO ty ot) β n.
  Proof.
    constructor. iIntros (l) "Hl". unfold optionalO; simpl_type.
    destruct e; by iApply (loc_in_bounds_in_bounds with "Hl").
  Qed. *)

  (* TODO: should be allow different opttys? *)
  Global Instance simple_subsume_place_optionalO A cty (ty1 : A → _) ty2 optty b
    `{!Affine P} `{!∀ x, SimpleSubsumePlace (ty1 x) (ty2 x) P}:
    SimpleSubsumePlace (b @ optionalO cty ty1 optty) (b @ optionalO cty ty2 optty) P.
  Proof.
    iIntros (l β) "HP Hl". destruct b. 2: by iFrame.
    unfold optionalO; simpl_type. iApply (@simple_subsume_place with "HP Hl").
  Qed.

  (* TODO: Should we have more instances like this? E.g. for the goal? *)
  Lemma simpl_hyp_optionalO_Some A cty (ty : A → type) optty l β x T:
    (l ◁ₗ{β} ty x -∗ T) ⊢ simplify_hyp (l ◁ₗ{β} Some x @ optionalO cty ty optty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simpl_hyp_optionalO_Some_inst := [instance simpl_hyp_optionalO_Some with 0%N].
  Global Existing Instance simpl_hyp_optionalO_Some_inst.
  Lemma simpl_hyp_optionalO_None A cty (ty : A → type) optty l β T:
    (l ◁ₗ{β} optty -∗ T) ⊢ simplify_hyp (l ◁ₗ{β} None @ optionalO cty ty optty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simpl_hyp_optionalO_None_inst := [instance simpl_hyp_optionalO_None with 0%N].
  Global Existing Instance simpl_hyp_optionalO_None_inst.
  Lemma simpl_hyp_optionalO_Some_val A cty (ty : A → type) optty v x T:
    (v ◁ᵥ|cty| ty x -∗ T) ⊢ simplify_hyp (v ◁ᵥ|cty| Some x @ optionalO cty ty optty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simpl_hyp_optionalO_Some_val_inst := [instance simpl_hyp_optionalO_Some_val with 0%N].
  Global Existing Instance simpl_hyp_optionalO_Some_val_inst.
  Lemma simpl_hyp_optionalO_None_val A cty (ty : A → type) optty v T:
    (v ◁ᵥ|cty| optty -∗ T) ⊢ simplify_hyp (v ◁ᵥ|cty| None @ optionalO cty ty optty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simpl_hyp_optionalO_None_val_inst := [instance simpl_hyp_optionalO_None_val with 0%N].
  Global Existing Instance simpl_hyp_optionalO_None_val_inst.

  Lemma subsume_optionalO_optty B A cty (ty : B → A → type) optty l β b T:
    (∃ x, <affine> ⌜b x = None⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} optty) (λ x : B, l ◁ₗ{β} (b x) @ optionalO cty (ty x) optty) T.
  Proof. iIntros "[% [%Heq ?]] Hl". iExists _. iFrame. by rewrite Heq. Qed.
  Definition subsume_optionalO_optty_inst := [instance subsume_optionalO_optty].
  Global Existing Instance subsume_optionalO_optty_inst.

  Lemma subsume_optionalO_ty B A cty (ty : B → A → type) optty l β b ty'
    `{!∀ x y, OptionableAgree (ty y x) ty'} T:
    (l ◁ₗ{β} ty' -∗ ∃ y x, <affine> ⌜b y = Some x⌝ ∗ l ◁ₗ{β} ty y x ∗ T y)
    ⊢ subsume (l ◁ₗ{β} ty') (λ y : B, l ◁ₗ{β} (b y) @ optionalO cty (ty y) (optty y)) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (?? Heq) "[??]".
    iExists _. iFrame. by rewrite Heq.
  Qed.
  Definition subsume_optionalO_ty_inst := [instance subsume_optionalO_ty].
  Global Existing Instance subsume_optionalO_ty_inst.

  Lemma subsume_optionalO_optty_val B A cty (ty : B → A → type) optty v b T:
    (∃ x, <affine> ⌜b x = None⌝ ∗ T x) ⊢ subsume (v ◁ᵥ|cty| optty) (λ x : B, v ◁ᵥ|cty| (b x) @ optionalO cty (ty x) optty) T.
  Proof. iIntros "[% [%Heq ?]] Hl". iExists _. iFrame. by rewrite Heq. Qed.
  Definition subsume_optionalO_optty_val_inst := [instance subsume_optionalO_optty_val].
  Global Existing Instance subsume_optionalO_optty_val_inst.

  Lemma subsume_optionalO_ty_val B A cty (ty : B → A → type) optty v b ty'
    `{!∀ y x, OptionableAgree (ty y x) ty'} T:
    (v ◁ᵥ|cty| ty' -∗ ∃ y x, <affine> ⌜b y = Some x⌝ ∗ v ◁ᵥ|cty| ty y x ∗ T y)
      ⊢ subsume (v ◁ᵥ|cty| ty') (λ y : B, v ◁ᵥ|cty| (b y) @ optionalO cty (ty y) (optty y)) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (?? Heq) "[??]".
    iExists _. iFrame. by rewrite Heq.
  Qed.
  Definition subsume_optionalO_ty_val_inst := [instance subsume_optionalO_ty_val].
  Global Existing Instance subsume_optionalO_ty_val_inst.

  Lemma subsume_optional_optionalO_val B cty ty optty b v T:
    (∃ x, T x) ⊢
      subsume (v ◁ᵥ|cty| b @ optional ty optty) (λ x : B, v ◁ᵥ|cty| optionalO cty (λ _ : (), ty) optty) T.
  Proof.
    rewrite /optional; simpl_type.
    rewrite /ty_own_val_at /ty_own_val /=.
    iIntros "[%?] [(% & ?)|(% & ?)]";
      iExists _; iFrame; [iExists (Some ())|iExists None]; iFrame.
  Qed.
  Definition subsume_optional_optionalO_val_inst := [instance subsume_optional_optionalO_val].
  Global Existing Instance subsume_optional_optionalO_val_inst.

  Inductive trace_optionalO :=
  | TraceOptionalO.

  Lemma type_eq_optionalO A (v1 v2 : val) (cty : Ctypes.type) (ty : A → type) optty (ot1 ot2 : Ctypes.type)
    `{!∀ x, Optionable cty (ty x) optty ot1 ot2}
    `{!Affine (v2 ◁ᵥₐₗ|cty| optty)} (b : option A) `{!Inhabited A} (T : _ → _ → assert):
   ⎡opt_pre (ty (option.default inhabitant b)) v1 v2⎤ ∧ 
    case_destruct b (λ b _,
        li_trace (TraceOptionalO, b) (∀ v, ⎡if b is Some x then v1 ◁ᵥₐₗ|cty| ty x else v1 ◁ᵥₐₗ|cty| optty⎤ -∗
         T v ((if b is Some x then false else true) @ boolean tint)))
      ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|cty| b @ optionalO cty ty optty⎤ v2 ⎡v2 ◁ᵥₐₗ|cty| optty⎤ Oeq ot1 ot2 tint T.
  Proof.
    unfold li_trace. iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ".
    destruct b.
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z false) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op true true with "Hpre [$Hv1] [$Hv2] Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      iDestruct "HT" as "[_ [% HT]]".
      iDestruct ("HT" with "Hv1") as "HT". iFrame.
      iApply "HΦ" => //. rewrite /ty_own_val_at /ty_own_val /=. iSplit; first done.
      iExists _. iSplit; iPureIntro; done.
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z true) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op false true with "Hpre [$Hv1] [$Hv2] Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      iDestruct "HT" as "[_ [% HT]]".
      iDestruct ("HT" with "Hv1") as "HT". iFrame.
      iApply "HΦ" => //. rewrite /ty_own_val_at /ty_own_val /=. iSplit; first done.
      iExists _. iSplit; iPureIntro; done.
  Qed.
  Definition type_eq_optionalO_inst := [instance type_eq_optionalO].
  Global Existing Instance type_eq_optionalO_inst.

  Lemma type_neq_optionalO A v1 v2 cty (ty : A → type) optty ot1 ot2 `{!∀ x, Optionable cty (ty x) optty ot1 ot2}
    `{!Affine (v2 ◁ᵥₐₗ|cty| optty)} b `{!Inhabited A} T :
    ⎡opt_pre (ty (option.default inhabitant b)) v1 v2⎤ ∧
    case_destruct b (λ b _,
      li_trace (TraceOptionalO, b) (∀ v, ⎡if b is Some x then v1 ◁ᵥₐₗ|cty| ty x else v1 ◁ᵥₐₗ|cty| optty⎤ -∗ T v ((if b is Some x then true else false) @ boolean tint)))
    ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|cty| b @ optionalO cty ty optty⎤ v2 ⎡v2 ◁ᵥₐₗ|cty| optty⎤ Cop.One ot1 ot2 tint T.
  Proof.
    unfold li_trace. iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ".
    destruct b.
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z true) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op true false with "Hpre [$Hv1] [$Hv2] Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      iDestruct "HT" as "[_ [% HT]]".
      iDestruct ("HT" with "Hv1") as "HT". iFrame.
      iApply "HΦ" => //. rewrite /ty_own_val_at /ty_own_val /=. iSplit; first done.
      iExists _. iSplit; iPureIntro; done.
    - iIntros "!>" (?) "Hctx !>".
      iExists (i2v (bool_to_Z false) tint).
      iSplit. {
        iStopProof; split => rho; monPred.unseal.
        iIntros "([Hpre _] & Hv1 & Hv2 & _ & Hctx)".
        iDestruct (opt_bin_op false false with "Hpre [$Hv1] [$Hv2] Hctx") as %Hiff.
        iPureIntro; intros. simpl in Hiff. rewrite Hiff //.
      }
      iDestruct "HT" as "[_ [% HT]]".
      iDestruct ("HT" with "Hv1") as "HT". iFrame.
      iApply "HΦ" => //. rewrite /ty_own_val_at /ty_own_val /=. iSplit; first done.
      iExists _. iSplit; iPureIntro; done.
  Qed.
  Definition type_neq_optionalO_inst := [instance type_neq_optionalO].
  Global Existing Instance type_neq_optionalO_inst.

  (* FIX ME: We don't have typed_read_end *)
(*
  Lemma read_optionalO_case A E l b (ty : A → type) optty ly mc a (T : val → type → _):
    case_destruct b (λ b _, li_trace (TraceOptionalO, b)
     (typed_read_end a E l Own (if b is Some x then ty x else optty) ly mc T))
    ⊢ typed_read_end a E l Own (b @ optionalO ty optty) ly mc T.
  Proof. iDestruct 1 as (_) "?". by destruct b. Qed.
  (* This should be tried very late *)
  Definition read_optionalO_case_inst := [instance read_optionalO_case].
  Global Existing Instance read_optionalO_case_inst | 1001.
*)
  (* Global Program Instance optionalO_copyable A cty (ty : A → type) optty x `{!∀ x, Copyable cty (ty x)} `{!Copyable cty optty} : Copyable cty (x @ optionalO cty ty optty).
  Next Obligation. Admitted.
  Next Obligation.
    iIntros (A ? ty optty x ? ? E l ?). unfold optionalO; simpl_type. destruct x.
    all: iIntros "Hl".
    all: iMod (copy_shr_acc with "Hl") as (? Hl ? ?) "[?[??]]" => //; try apply: Hty.
    all: iModIntro; iExists _; iSplit => //=.
    all: iExists _, _; iFrame.
  Qed. *)
End optionalO.
Global Typeclasses Opaque optionalO_type optionalO.
Notation "optionalO< ty , optty >" := (optionalO ty optty)
  (only printing, format "'optionalO<' ty ,  optty '>'") : printing_sugar.
