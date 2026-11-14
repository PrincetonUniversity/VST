(** * Why adequacy of EXWP needs non-constructible state interpretations

    EXWP's sequential case quantifies over every [sq_heap_gen m h], i.e. over
    the full authority [● sq_heap_cells m h] for the executing thread's own
    permission map [h]. Inside the logic, a full authority is only obtainable
    for an [h] covering every live points-to fragment ([sq_heap_gen_lookup]),
    and fragments of other threads are hidden inside their (opaque) WPs. So an
    adequacy argument that only ever supplies state interpretations it can
    build from the machine-level resources must use [h = sq_full_heap m] (or
    something no more informative): the global view.

    This file makes the consequence precise:

    - [exwp_gen SI] is EXWP with the state interpretation as a parameter;
      [exwp_gen_sq_heap_gen] shows EXWP is the instance [SI := sq_heap_gen].
    - [sq_heap_global] is the global view: [sq_heap_gen m h] with
      [h = sq_full_heap m]. It satisfies the same interface as [sq_heap_gen]
      ([sqex_si_interface]); the only difference is that it forgets the
      non-global instances of the quantifier.
    - [exwp_global_weaken]: EXWP implies its global-view variant.
    - [race_prog] is verified by the global-view variant
      ([race_prog_global_exwp]), but it is unsafe on the atomic machine
      ([race_prog_unsafe]): a non-atomic read races with a non-atomic write.
    - Hence no adequacy proof that is parametric in a state interpretation
      satisfying the interface exists ([sqex_parametric_adequacy_fails]),
      and EXWP itself cannot verify [race_prog] ([race_prog_not_exwp]); the
      latter uses [sqex_adequacy], whose proof evaluates the thread's WP on a
      hypothetical local authority, i.e. on the resource that makes it true.

    [sqfp_logic.v] and [sqfp_adequacy.v] give a variant of EXWP whose
    adequacy is proved inside the logic: the thread hands over the points-to
    footprint of each step until Commit, instead of quantifying over local
    permission maps. *)

From iris.algebra Require Import auth gmap.
From iris.proofmode Require Import proofmode coq_tactics reduction.
From lrust.lang Require Import notation tactics.
Require Import VST.atomic_machine.atomic_machine.
Require Import VST.atomic_machine.lambda_rust.logic.at_logic.
Require Import VST.atomic_machine.lambda_rust.equivalence.
Require Import VST.atomic_machine.lambda_rust.adequacy.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_rules.
Require Import VST.atomic_machine.lambda_rust.logic.sqex_adequacy.

Set Default Proof Using "Type".
#[local] Set Warnings "-redundant-canonical-projection".

Local Existing Instance lrSqGS_invGS.
Local Existing Instance lr_ext_specs.

(** ** EXWP with an arbitrary state interpretation *)

Section exwp_gen.
  Context `{!lrSqGS Σ}.

  Definition exwp_gen (SI : lr_mem -> perm_map -> iProp Σ) :
      coPset -> sq_expr -> (sq_val -> iProp Σ) -> iProp Σ :=
    fixpoint (exwp_pre lr_ext_specs to_val SI).

  Lemma exwp_gen_unfold SI E e Φ :
    exwp_gen SI E e Φ ⊣⊢ exwp_pre lr_ext_specs to_val SI (exwp_gen SI) E e Φ.
  Proof. apply (fixpoint_unfold (exwp_pre lr_ext_specs to_val SI)). Qed.

  (** EXWP is the instance at [sq_heap_gen]. *)
  Lemma exwp_gen_sq_heap_gen E e Φ :
    EXWP e @ E {{ Φ }} ⊣⊢ exwp_gen sq_heap_gen E e Φ.
  Proof.
    have Hfix : (exwp : coPset -d> sq_expr -d> (sq_val -d> iPropO Σ) -d> iPropO Σ)
      ≡ exwp_gen sq_heap_gen.
    { apply fixpoint_unique. intros E' e' Φ'. apply exwp_unfold. }
    apply Hfix.
  Qed.

  Context (SI : lr_mem -> perm_map -> iProp Σ).
  Local Notation WPG := (exwp_gen SI).

  Lemma exwp_gen_value E v Φ : Φ v ⊢ WPG E (of_val v) Φ.
  Proof. rewrite exwp_gen_unfold /exwp_pre to_of_val. apply bupd_intro. Qed.

  Lemma exwp_gen_bupd E e Φ : (|==> WPG E e Φ) ⊢ WPG E e Φ.
  Proof. rewrite exwp_gen_unfold /exwp_pre. destruct (to_val e); apply bupd_trans. Qed.

  Lemma exwp_gen_wand E e Φ Ψ :
    WPG E e Φ -∗ (∀ v, Φ v -∗ Ψ v) -∗ WPG E e Ψ.
  Proof.
    iLöb as "IH" forall (e). iIntros "Hwp HΦ".
    rewrite !(exwp_gen_unfold SI E e) /exwp_pre.
    destruct (to_val e) as [v|].
    { iMod "Hwp". iModIntro. by iApply "HΦ". }
    iMod "Hwp" as "[[%Hno Hseq] | (%op & %k & %He & Hspec)]"; iModIntro.
    - iLeft. iSplit; first done. iIntros (m h) "Hm".
      iMod ("Hseq" with "Hm") as "[$ Hstep]". iModIntro.
      iIntros (T e2 m2 Hs). iSpecialize ("Hstep" $! T e2 m2 with "[//]"). iNext.
      iMod "Hstep" as (h2) "(Hp & Hm & Hwp)". iModIntro. iExists h2. iFrame.
      iApply ("IH" with "Hwp HΦ").
    - iRight. iExists op, k. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp". iModIntro.
      iApply ("IH" with "Hwp HΦ").
  Qed.

  Lemma exwp_gen_bind K E e Φ :
    WPG E e (λ v, WPG E (fill K (of_val v)) Φ) ⊢ WPG E (fill K e) Φ.
  Proof.
    iLöb as "IH" forall (e). rewrite (exwp_gen_unfold SI E e) /exwp_pre.
    destruct (to_val e) as [v|] eqn:Hv.
    { apply of_to_val in Hv. subst e. iApply exwp_gen_bupd. }
    rewrite exwp_gen_unfold /exwp_pre (fill_not_val _ _ Hv).
    iIntros ">[[%Hno Hseq] | (%op & %k & %He & Hspec)] !>".
    - iLeft. iSplit.
      { iPureIntro. intros op k He.
        destruct (lr_external_fill_inv _ _ _ _ Hv He) as (k' & He' & _).
        by eapply Hno. }
      iIntros (m h) "Hm". iMod ("Hseq" with "Hm") as "[%Hr Hstep]".
      iModIntro. iSplit.
      { iPureIntro. destruct Hr as (T & e2 & m2 & Hs).
        exists T, (fill K e2), m2. destruct Hs. rewrite -!fill_app. by constructor. }
      iIntros (T e2 m2 Hs).
      inversion Hs as [K' r m0 T0 r' m0' Hh Heq]; subst.
      destruct (fill_decompose K K' e r (lr_head_step_redex_shape _ _ _ _ _ Hh)
        (lr_head_step_not_val _ _ _ _ _ Hh) Hv (eq_sym Heq)) as (K'' & -> & ->).
      iDestruct ("Hstep" $! T (fill K'' r') m2 with "[%]") as "Hstep".
      { by constructor. }
      iNext. iMod "Hstep" as (h2) "(Hperm & Hm & Hwp)".
      iModIntro. iExists h2. iFrame. rewrite fill_app. by iApply "IH".
    - destruct (lr_external_fill K _ _ _ He) as (k' & He' & Hk).
      iRight. iExists op, k'. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iFrame "Hpre".
      iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
      iModIntro. rewrite Hk. by iApply "IH".
  Qed.

  Lemma exwp_gen_pure_step E e1 e2 Φ :
    @pure_step sq_lang e1 e2 -> ▷ WPG E e2 Φ ⊢ WPG E e1 Φ.
  Proof.
    intros [Hsafe Hdet].
    assert (Hv : to_val e1 = None).
    { destruct (Hsafe ∅) as (e' & m' & efs & Hs). exact (language.val_stuck _ _ _ _ _ _ Hs). }
    rewrite (exwp_gen_unfold SI E e1) /exwp_pre Hv.
    iIntros "Hwp !>". iLeft. iSplit.
    { iPureIntro. destruct (Hsafe ∅) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      intros op k He. by eapply lr_step_external_disjoint. }
    iIntros (m h) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (Hsafe m) as (e' & m' & efs & [Hs _]%sq_prim_step_lr_step).
      eauto. }
    iIntros (T e' m' Hs).
    destruct (Hdet m T e' m' []) as (-> & -> & -> & _).
    { by apply sq_prim_step_lr_step. }
    iNext. iModIntro. iExists h. iFrame. iPureIntro. constructor.
  Qed.

  Lemma exwp_gen_pure_steps E e1 e2 Φ n :
    nsteps (@pure_step sq_lang) n e1 e2 -> ▷^n WPG E e2 Φ ⊢ WPG E e1 Φ.
  Proof.
    induction 1 as [e | n e1 e2 e3 Hs Hsteps IH]; first done.
    simpl. iIntros "H". iApply (exwp_gen_pure_step _ _ _ _ Hs).
    iNext. by iApply IH.
  Qed.

  Lemma exwp_gen_lift_external E e op k Φ :
    lr_external e op k ->
    (|={E,∅}=> ∃ x : ext_spec_args op,
      ext_spec_pre op x (λ ef, ▷ WPG ⊤ ef (λ _, True)) ∗
      ▷ (∀ ov, ext_spec_post op x ov -∗ |={∅,E}=> WPG E (k ov) Φ)) ⊢
    WPG E e Φ.
  Proof.
    intros Hext. rewrite (exwp_gen_unfold SI E e) /exwp_pre (lr_external_not_val _ _ _ Hext).
    iIntros "Hspec !>". iRight. iExists op, k. by iFrame.
  Qed.

  Lemma tac_exwp_gen_bind K Δ E Φ e :
    envs_entails Δ (WPG E e (λ v, WPG E (fill K (of_val v)) Φ)) ->
    envs_entails Δ (WPG E (fill K e) Φ).
  Proof. rewrite envs_entails_unseal => ->. apply exwp_gen_bind. Qed.

  Lemma tac_exwp_gen_pure K Δ Δ' E e1 e2 φ n Φ :
    @PureExec sq_lang φ n e1 e2 -> φ ->
    MaybeIntoLaterNEnvs n Δ Δ' ->
    envs_entails Δ' (WPG E (fill K e2) Φ) ->
    envs_entails Δ (WPG E (fill K e1) Φ).
  Proof.
    rewrite envs_entails_unseal => Hexec Hφ ? HΔ.
    rewrite into_laterN_env_sound HΔ. apply exwp_gen_pure_steps.
    exact (@pure_step_nsteps_ctx sq_lang (@ectx_language.fill sq_ectx_lang K)
      (@ectx_lang_ctx sq_ectx_lang K) n e1 e2 (Hexec Hφ)).
  Qed.
End exwp_gen.

Tactic Notation "exwpg_bind" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp_gen ?SI ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; apply (tac_exwp_gen_bind SI K); simpl)
  end.

Tactic Notation "exwpg_pure" open_constr(efoc) :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (exwp_gen ?SI ?E ?e ?Φ) => reshape_expr e ltac:(fun K e' =>
    unify e' efoc; eapply (tac_exwp_gen_pure SI K);
    [simpl; tc_solve | try done | tc_solve | simpl_subst])
  end.

(** ** The global view *)

Lemma sq_full_heap_insert (m : lr_mem) l v :
  sq_full_heap (<[l := v]> m) = <[l := 1%Qp]> (sq_full_heap m).
Proof. by rewrite /sq_full_heap fmap_insert. Qed.

Lemma sq_full_heap_alloc (m : lr_mem) l n :
  sq_full_heap (alloc_gmap (LitV LitPoison) l n m) = alloc_gmap 1%Qp l n (sq_full_heap m).
Proof.
  revert l. induction n as [|n IH]=> l //=. by rewrite sq_full_heap_insert IH.
Qed.

Lemma sq_full_heap_free (m : lr_mem) l n :
  sq_full_heap (free_gmap l n m) = free_gmap l n (sq_full_heap m).
Proof.
  revert l. induction n as [|n IH]=> l //=. by rewrite /sq_full_heap fmap_delete -IH.
Qed.

(** Every permitted step keeps the permission map equal to the full map of the
    current memory, so the global view is closed under sequential steps. *)
Lemma perm_step_full m T m' h' :
  lr_mem_effect m T m' -> perm_step T (sq_full_heap m) h' -> h' = sq_full_heap m'.
Proof.
  intros Heffect Hperm. destruct Heffect as [m|m l Hl|m l v Hl|m l n Hfresh|m l n Hfree].
  - by inversion Hperm.
  - apply perm_step_singleton in Hperm. by inversion Hperm.
  - apply perm_step_singleton in Hperm. inversion Hperm; subst.
    destruct Hl as [w Hw].
    rewrite sq_full_heap_insert insert_id; first done.
    by rewrite /sq_full_heap lookup_fmap Hw.
  - rewrite (sqex_seq_perm_alloc_result _ _ _ _ Hperm). by rewrite sq_full_heap_alloc.
  - rewrite (sqex_seq_perm_free_result _ _ _ _ Hperm). by rewrite sq_full_heap_free.
Qed.

Section global_view.
  Context `{!lrSqGS Σ}.

  (** The state interpretation obtained from the shared heap authority alone. *)
  Definition sq_heap_global (m : lr_mem) (h : perm_map) : iProp Σ :=
    sq_heap_gen m h ∗ ⌜h = sq_full_heap m⌝.

  (** The interface an abstract adequacy proof may use about a state
      interpretation: it describes the heap ([sq_heap_gen] and hence every
      read/lookup lemma), it is an invariant of [sq_heap_gen] that is closed
      under every permitted sequential step (so all heap update lemmas and
      all EXWP rules carry over), and it can be built from the global heap
      authority, which is what initialization and every other machine-level
      construction provides. *)
  Record sqex_si_interface (SI : lr_mem -> perm_map -> iProp Σ) : Prop := {
    si_heap m h : SI m h ⊢ sq_heap_gen m h ∗
      (∀ T m' h', ⌜lr_mem_effect m T m' ∧ perm_step T h h'⌝ -∗
        sq_heap_gen m' h' -∗ SI m' h');
    si_global m : sq_heap_gen m (sq_full_heap m) ⊢ SI m (sq_full_heap m)
  }.

  Lemma sq_heap_gen_interface : sqex_si_interface sq_heap_gen.
  Proof.
    split.
    - iIntros (m h) "$". iIntros (T m' h' _) "$".
    - done.
  Qed.

  Lemma sq_heap_global_interface : sqex_si_interface sq_heap_global.
  Proof.
    split.
    - iIntros (m h) "[$ ->]". iIntros (T m' h' [Heffect Hperm]) "$".
      iPureIntro. by eapply perm_step_full.
    - iIntros (m) "$". done.
  Qed.

  (** EXWP is stronger than its global-view variant: the latter only uses the
      instance [h = sq_full_heap m] of EXWP's universal quantifier. *)
  Lemma exwp_global_weaken E e Φ :
    EXWP e @ E {{ Φ }} ⊢ exwp_gen sq_heap_global E e Φ.
  Proof.
    iLöb as "IH" forall (E e Φ).
    rewrite exwp_unfold exwp_gen_unfold /exwp_pre.
    destruct (to_val e) as [v|]; first (iIntros "H"; iExact "H").
    iIntros ">[[%Hno Hseq] | (%op & %k & %He & Hspec)] !>".
    - iLeft. iSplit; first done. iIntros (m h) "[Hm %Hh]".
      iMod ("Hseq" with "Hm") as "[$ Hstep]". iModIntro.
      iIntros (T e2 m2 Hs). iSpecialize ("Hstep" $! T e2 m2 with "[//]"). iNext.
      iMod "Hstep" as (h2) "(%Hperm & Hm & Hwp)". iModIntro. iExists h2.
      iSplit; first done. iSplitL "Hm".
      { iFrame. iPureIntro. subst h. by eapply perm_step_full; [eapply lr_step_mem_effect |]. }
      by iApply "IH".
    - iRight. iExists op, k. iSplit; first done.
      iMod "Hspec" as (x) "[Hpre Hcont]". iModIntro. iExists x. iSplitL "Hpre".
      + destruct op; simpl; try done. iNext. by iApply "IH".
      + iNext. iIntros (ov) "Hpost". iMod ("Hcont" with "Hpost") as "Hwp".
        iModIntro. by iApply "IH".
  Qed.
End global_view.

(** ** A racy program verified by the global view *)

(** The parent allocates [l], hands [l ↦ ☠] to a child that writes it
    non-atomically, and then reads [l] non-atomically, keeping only the
    freeable token. *)
Definition race_body : expr := (Fork ("l" <- #1) ;; !"l")%E.
Definition race_prog : sq_expr := (let: "l" := Alloc #1 in race_body)%E.

Section race_proof.
  Context `{!lrSqGS Σ}.

  Lemma sqex_freeable_allocated m h l :
    sq_heap_gen m h -∗ †l…1 -∗ ⌜is_Some (m !! l)⌝.
  Proof.
    iIntros "(%hF & Hm & HF & [%Hrel %HFrel]) Hfree".
    iCombine "HF Hfree" gives %[Hin Hvalid]%auth_both_valid_discrete.
    move: Hin=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hlookup Hin]].
    apply (Some_included_exclusive _ _) in Hin as [=<-<-]%leibniz_equiv; last first.
    { move: (Hvalid (l.1)). rewrite Hlookup. by intros [??]. }
    iPureIntro.
    pose proof (sq_freeable_is_Some m hF l 1 0 HFrel Hlookup) as Hsome.
    rewrite shift_loc_0 in Hsome. apply Hsome. lia.
  Qed.

  (** A real EXWP rule: allocation also yields the freeable token. *)
  Lemma exwp_alloc_freeable E Φ :
    (▷ ∀ l, l ↦ LitV LitPoison -∗ †l…1 -∗ Φ (LitV (LitLoc l))) -∗
    EXWP (Alloc (Lit (LitInt 1))) @ E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply exwp_lift_step; first done.
    { intros op k He. apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m h) "Hm". iModIntro. iSplit.
    { iPureIntro. destruct (sq_alloc_fresh m) as [l Hl].
      do 3 eexists. apply (LREctxStep []). apply LRAllocS; [lia | done]. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs; subst. iNext.
    iDestruct (sq_heap_gen_missing m h l with "Hm") as %Hnone.
    { by rewrite -(shift_loc_0 l). }
    iMod (sq_heap_gen_alloc _ _ _ 1 with "Hm") as "[Hm [Hfree Hl]]"; [lia | done | ].
    rewrite sq_pointsto_vec_cons. iDestruct "Hl" as "[Hl _]".
    iModIntro. iExists (<[l := 1%Qp]> h). iSplit.
    { iPureIntro. econstructor; [by apply PermAlloc | constructor]. }
    iFrame. iApply (exwp_value _ (LitV (LitLoc l))). iApply ("HΦ" with "Hl Hfree").
  Qed.

  (** The global view accepts a non-atomic read justified only by the
      freeable token: the read check [h !! l = Some _] holds for the global
      permission map at every allocated location. EXWP rejects this rule:
      it must also handle permission maps without [l]. *)
  Lemma exwp_global_read_freeable E l :
    †l…1 -∗ exwp_gen sq_heap_global E (Read Na1Ord (Lit (LitLoc l))) (λ _, True).
  Proof.
    iIntros "Hfree". rewrite exwp_gen_unfold /exwp_pre /=.
    iModIntro. iLeft. iSplit.
    { iPureIntro. intros op k He.
      apply lr_external_head in He; [inversion He | solve_redex_shape]. }
    iIntros (m h) "[Hm %Hh]".
    iDestruct (sqex_freeable_allocated with "Hm Hfree") as %[v Hv].
    iModIntro. iSplit.
    { iPureIntro. do 3 eexists. apply (LREctxStep []). by apply LRReadNaS. }
    iIntros (T e2 m2 Hs). apply lr_step_head in Hs; last solve_redex_shape.
    inversion Hs as [| |l' v' m' Hl' | | | |]; subst T e2 m2 l' m'.
    iNext. iModIntro. iExists h.
    iSplit.
    { iPureIntro. econstructor; last constructor. subst h. eapply PermRead.
      rewrite /sq_full_heap lookup_fmap Hv /=. done. }
    iFrame "Hm". iSplit; first done. by iApply exwp_gen_value.
  Qed.

  Lemma race_prog_global_exwp :
    ⊢ exwp_gen sq_heap_global ⊤ race_prog (λ _, True).
  Proof.
    rewrite /race_prog /race_body.
    exwpg_bind (Alloc _). iApply exwp_global_weaken.
    iApply exwp_alloc_freeable. iIntros "!>" (l) "Hl Hfree".
    exwpg_pure (App _ _).
    exwpg_bind (Fork _).
    iApply (exwp_gen_lift_external _ _ _ (ASpawn (Write Na1Ord (Lit (LitLoc l)) (Lit (LitInt 1))))
      (fun _ => Lit LitPoison)).
    { apply (LREctxExternal []). constructor. }
    iApply fupd_mask_intro; first set_solver. iIntros "Hclose".
    iExists (). simpl. iSplitL "Hl".
    { iNext. iApply (exwp_gen_wand with "[Hl]").
      { iApply exwp_global_weaken.
        iApply (exwp_write_na _ l (LitV LitPoison) (LitV (LitInt 1)) with "Hl"). }
      auto. }
    iIntros "!>" (ov) "->". iMod "Hclose" as "_". iModIntro.
    iApply (exwp_gen_value _ _ (LitV LitPoison)). simpl.
    exwpg_pure (App _ _).
    by iApply exwp_global_read_freeable.
  Qed.
End race_proof.

(** ** The racy program is unsafe on the atomic machine *)

Definition race_loc : loc := (1%positive, 0%Z).
Definition race_read : expr := Read Na1Ord (Lit (LitLoc race_loc)).
Definition race_write : expr := Write Na1Ord (Lit (LitLoc race_loc)) (Lit (LitInt 1)).
Definition race_main1 : expr := App (Rec BAnon [BNamed "l"] race_body) [Lit (LitLoc race_loc)].
Definition race_main2 : expr := App (Rec BAnon [BAnon] race_read) [Fork race_write].
Definition race_main3 : expr := App (Rec BAnon [BAnon] race_read) [Lit LitPoison].
Local Instance race_body_closed : Closed (BAnon :b: [BNamed "l"] +b+ []) race_body.
Proof. by vm_compute. Qed.
Local Instance race_read_closed : Closed (BAnon :b: [BAnon] +b+ []) race_read.
Proof. by vm_compute. Qed.

Definition race_mem1 : lr_mem := alloc_gmap (LitV LitPoison) race_loc (Z.to_nat 1) ∅.
Definition race_mem2 : lr_mem := <[race_loc := LitV (LitInt 1)]> race_mem1.

(** The child's write is pending when the parent reaches its read. *)
Lemma race_prog_reaches_race :
  exists tp mu,
    am_steps (AMCfg (sqex_pool [race_prog]) ∅ (sq_mu ∅)) (AMCfg tp race_mem2 mu) /\
    tp !! 0%nat = Some (Running race_read []) /\ mu !! race_loc = Some Wst.
Proof.
  eexists _, _. split; [|split].
  - (* Parent: Try the allocation. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 0%nat race_prog (lr_alloc_events race_loc (Z.to_nat 1))
        race_main1 race_mem1).
      - by vm_compute.
      - change race_prog with (fill [LetCtx (BNamed "l") race_body] (Alloc (Lit (LitInt 1)))).
        change race_main1 with (fill [LetCtx (BNamed "l") race_body] (Lit (LitLoc race_loc))).
        apply LREctxStep. apply LRAllocS; [lia | done].
      - reflexivity. }
    (* Parent: Commit the allocation. *)
    eapply rtc_l.
    { eapply (Core_Commit _ _ _ 0%nat race_main1).
      - by rewrite lookup_insert_eq.
      - done.
      - reflexivity. }
    (* Parent: beta-reduce the [let]. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 0%nat race_main1 [] race_main2 race_mem1).
      - by rewrite lookup_insert_eq.
      - apply (LREctxStep [] race_main1). apply LRBetaS.
        + by repeat constructor.
        + apply _.
        + by vm_compute.
      - reflexivity. }
    (* Parent: spawn the child as thread 1. *)
    eapply rtc_l.
    { eapply (Spawn _ _ _ 0%nat race_main2 race_write
        (fun ov => fill [AppRCtx (LamV [BAnon] race_read) [] []]
          ((fun _ => Lit LitPoison) ov)) 1%nat).
      - by rewrite lookup_insert_eq.
      - change race_main2 with
          (fill [AppRCtx (LamV [BAnon] race_read) [] []] (Fork race_write)).
        apply LREctxExternal. constructor.
      - by vm_compute.
      - intros k Hk. assert (k = 0%nat) as -> by lia. by rewrite lookup_insert_eq. }
    (* Parent: beta-reduce the sequence. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 0%nat race_main3 [] race_read race_mem1).
      - by vm_compute.
      - apply (LREctxStep [] race_main3). apply LRBetaS.
        + by repeat constructor.
        + apply _.
        + by vm_compute.
      - reflexivity. }
    (* Child: Try the non-atomic write; it reserves [race_loc] as [Wst]. *)
    eapply rtc_l.
    { eapply (Core_Try _ _ _ 1%nat race_write [lr_write_event race_loc]
        (Lit LitPoison) race_mem2).
      - by vm_compute.
      - apply (LREctxStep [] race_write).
        apply (LRWriteNaS _ _ _ (LitV LitPoison)); by vm_compute.
      - reflexivity. }
    apply rtc_refl.
  - by vm_compute.
  - by vm_compute.
Qed.

(** A non-atomic read of a location with a pending write cannot step. *)
Lemma race_read_stuck m mu :
  mu !! race_loc = Some Wst -> ¬ am_not_stuck (Running race_read []) m mu.
Proof.
  intros Hmu [(c & Heq & Hfinal) | (q' & Hstep)].
  - injection Heq as <-. destruct Hfinal as [v Hv]. discriminate.
  - inversion Hstep; subst; unfold tpool in *;
      apply lookup_singleton_Some in Hget as [_ Hget]; inversion Hget; subst;
      unfold race_read in *; try done;
      try (match goal with H : sqlang_at_external _ _ _ |- _ =>
        apply lr_external_head in H; [inversion H | solve_redex_shape] end).
    match goal with H : sqlang_step _ _ _ _ _ |- _ => rename H into Hseq end.
    apply lr_step_head in Hseq; last solve_redex_shape.
    inversion Hseq; subst. simpl in Hreserve.
    rewrite /rsv /= /rsv_Read Hmu in Hreserve. discriminate.
Qed.

Theorem race_prog_unsafe : ¬ at_sem_adequate [race_prog] [λ _, True] ∅.
Proof.
  intros Hadeq. destruct race_prog_reaches_race as (tp & mu & Hsteps & Hmain & Hmu).
  destruct (Hadeq _ _ _ Hsteps) as [Hsafe _].
  exact (race_read_stuck _ _ Hmu (Hsafe _ _ Hmain)).
Qed.

(** Why only the global view is available inside the logic: in the racy
    configuration the child holds [l ↦ v] (inside its WP). Any state
    interpretation that can coexist with it has [h !! l = Some 1], so the
    parent's read check succeeds for every instance one can construct. The
    instance that rejects the parent's read (a map without [l]) would need an
    authority incompatible with the child's fragment. *)
Lemma sq_heap_gen_other_thread_full `{!lrSqGS Σ} m h l v :
  l ↦ v -∗ sq_heap_gen m h -∗ ⌜h !! l = Some 1%Qp⌝.
Proof. iIntros "Hl Hm". iApply (sq_heap_gen_full with "Hm Hl"). Qed.

Lemma sq_heap_gen_other_thread_absent `{!lrSqGS Σ} m h l v :
  h !! l = None -> l ↦ v -∗ sq_heap_gen m h -∗ False.
Proof.
  iIntros (Hnone) "Hl Hm".
  iDestruct (sq_heap_gen_other_thread_full with "Hl Hm") as %Hfull. congruence.
Qed.

(** ** Consequences *)

(** Adequacy for a state interpretation, stated exactly as [sqex_adequacy]. *)
Definition sqex_adequate_for
    (SI : forall Σ, lrSqGS Σ -> lr_mem -> perm_map -> iProp Σ) : Prop :=
  forall Σ (_ : lrSqGpreS Σ) (e : sq_expr) (φ : sq_val -> Prop) (m : lr_mem),
    (forall `{H : !lrSqGS Σ}, ⊢ @exwp_gen Σ H (SI Σ H) ⊤ e (λ v, ⌜φ v⌝)) ->
    at_sem_adequate [e] [φ] m.

(** [sqex_adequacy] is adequacy for the instance [sq_heap_gen]. *)
Lemma sq_heap_gen_adequate :
  sqex_adequate_for (fun Σ H => @sq_heap_gen Σ (@lrSqGS_heapGS Σ H)).
Proof.
  intros Σ Hpre e φ m Hwp. apply (sqex_adequacy Σ). intros Hgs.
  iApply exwp_gen_sq_heap_gen. iApply Hwp.
Qed.

(** The global view satisfies the same interface, but is not adequate. *)
Lemma sq_heap_global_not_adequate :
  ¬ sqex_adequate_for (fun Σ H => @sq_heap_global Σ H).
Proof.
  intros Hadeq. apply race_prog_unsafe.
  apply (Hadeq lrSqΣ _). intros H. apply race_prog_global_exwp.
Qed.

(** Therefore no adequacy proof can treat the state interpretation as an
    abstract predicate with the interface [sqex_si_interface]. *)
Theorem sqex_parametric_adequacy_fails :
  ¬ (forall SI : (forall Σ, lrSqGS Σ -> lr_mem -> perm_map -> iProp Σ),
       (forall Σ (H : lrSqGS Σ), sqex_si_interface (SI Σ H)) ->
       sqex_adequate_for SI).
Proof.
  intros Hpar. apply sq_heap_global_not_adequate.
  apply Hpar. intros Σ H. apply sq_heap_global_interface.
Qed.

(** EXWP proves strictly less than its global-view variant: its soundness
    really depends on the instances that only exist for a thread in isolation. *)
Corollary race_prog_not_exwp Σ `{!lrSqGpreS Σ} :
  ¬ (forall `{!lrSqGS Σ}, ⊢ EXWP race_prog {{ _, True }}).
Proof. intros Hwp. apply race_prog_unsafe. by apply (sqex_adequacy Σ). Qed.
