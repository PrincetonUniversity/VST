(* modified from iris.base_logic.lib.ghost_map *)

(** A "resource map" (or "resource heap") with a proposition controlling authoritative
ownership of the entire heap, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Export auth csum gmap.
From iris_ora.algebra Require Export osum gmap.
From iris_ora.logic Require Export logic own.
From VST.veric Require Export shares share_alg auth.
From VST.veric Require Import view shared algebras.
From iris.prelude Require Import options.

(* We can probably drop the agree branch, and just use persistent shared and adjust the permission
   later. *)
Definition rmapUR (K : Type) `{Countable K} (V : ofe) : uora :=
  gmapUR K (csumR (sharedR V) (agreeR V)).

Lemma shared_order_includedN {V} n (x y : shared V) : ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
Proof.
  intros Hvalid [|(Hd & Hv)].
  - exists y; rewrite H comm shared_err_absorb //.
  - apply shared_includedN'; first done.
    split.
    + destruct Hd as [<-|<-]; [|eexists]; done.
    + rewrite option_includedN_total.
      apply shared_validN in Hvalid as [_ Hvalid].
      destruct (val_of x); last by auto.
      destruct (val_of y); last done.
      rewrite Some_orderN in Hv.
      right; eexists _, _; split; first done; split; first done.
      apply agree_order_dist in Hv as ->; done.
Qed.

Lemma rmap_order_includedN K `{Countable K} V n (x y : rmapUR K V) : ✓{n} y → x ≼ₒ{n} y → x ≼{n} y.
Proof.
  intros Hvalid Hord. rewrite lookup_includedN; intros i.
  specialize (Hvalid i); specialize (Hord i); rewrite option_includedN.
  destruct (x !! i) as [a|] eqn: Hx; last by auto.
  rewrite Hx in Hord |- *; clear Hx.
  destruct (_ !! _) as [b|]; last done.
  right; eexists _, _; split; first done; split; first done.
  rewrite csum_includedN; apply csum_orderN' in Hord as [ | [ (? & ? & -> & -> & Hord) | (? & ? & -> & -> & Hord) ]].
  - auto.
  - apply shared_order_includedN in Hord; eauto 8.
  - eapply agree_order_dist in Hord as ->; auto.
Qed.

Canonical Structure rmap_authR K `{Countable K} V := authR _ (rmap_order_includedN K V).
Canonical Structure rmap_authUR K `{Countable K} V := authUR _ (rmap_order_includedN K V).

Global Instance rmap_frag_core_id {K} `{Countable K} {V} (a : rmapUR K V) : OraCoreId a → OraCoreId (◯ a).
Proof. apply @auth_frag_core_id. Qed.

Class resource_mapG Σ K `{Countable K} (V : Type) := ResourceMapG {
  resource_map_inG : inG Σ (rmap_authR K (leibnizO V));
}.
Local Existing Instance resource_map_inG.

Definition resource_mapΣ K `{Countable K} (V : Type) : gFunctors :=
  #[ GFunctor (rmap_authR K (leibnizO V)) ].

Global Instance subG_resource_mapΣ Σ K `{Countable K} (V : Type) :
  subG (resource_mapΣ K V) Σ → resource_mapG Σ K V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{resource_mapG Σ K V}.

  Local Definition resource_map_auth_def
      (γ : gname) (q : Qp) m : iProp Σ :=
    own γ (●{dfrac.DfracOwn q} m).
  Local Definition resource_map_auth_aux : seal (@resource_map_auth_def).
  Proof. by eexists. Qed.
  Definition resource_map_auth := resource_map_auth_aux.(unseal).
  Local Definition resource_map_auth_unseal :
    @resource_map_auth = @resource_map_auth_def := resource_map_auth_aux.(seal_eq).

  Local Definition resource_map_elem_def
      (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
    ∃ rsh, own γ (◯ {[k := Cinl (YES (V := leibnizO V) dq rsh (to_agree v))]}).
  Local Definition resource_map_elem_aux : seal (@resource_map_elem_def).
  Proof. by eexists. Qed.
  Definition resource_map_elem := resource_map_elem_aux.(unseal).
  Local Definition resource_map_elem_unseal :
    @resource_map_elem = @resource_map_elem_def := resource_map_elem_aux.(seal_eq).

  Local Definition resource_map_elem_no_def
      (γ : gname) (k : K) (sh : share) : iProp Σ :=
    ∃ rsh, own γ (◯ {[k := Cinl (NO (V := leibnizO V) (Share sh) rsh)]}).
  Local Definition resource_map_elem_no_aux : seal (@resource_map_elem_no_def).
  Proof. by eexists. Qed.
  Definition resource_map_elem_no := resource_map_elem_no_aux.(unseal).
  Local Definition resource_map_elem_no_unseal :
    @resource_map_elem_no = @resource_map_elem_no_def := resource_map_elem_no_aux.(seal_eq).

  Local Definition resource_map_elem_pure_def
      (γ : gname) k v : iProp Σ :=
    own γ (◯ {[k := Cinr (to_agree v)]}).
  Local Definition resource_map_elem_pure_aux : seal (@resource_map_elem_pure_def).
  Proof. by eexists. Qed.
  Definition resource_map_elem_pure := resource_map_elem_pure_aux.(unseal).
  Local Definition resource_map_elem_pure_unseal :
    @resource_map_elem_pure = @resource_map_elem_pure_def := resource_map_elem_pure_aux.(seal_eq).
End definitions.

Notation "k ↪[ γ ] dq v" := (resource_map_elem γ k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ ] dq  v") : bi_scope.

Notation "k ↪[ γ ]p v" := (resource_map_elem_pure γ k v)
  (at level 20, γ at level 50,
   format "k  ↪[ γ ]p  v") : bi_scope.

(* no notation for no right now *)

Local Ltac unseal := rewrite
  ?resource_map_auth_unseal /resource_map_auth_def
  ?resource_map_elem_unseal /resource_map_elem_def
  ?resource_map_elem_no_unseal /resource_map_elem_no_def
  ?resource_map_elem_pure_unseal /resource_map_elem_pure_def.

Section lemmas.
  Context `{resource_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp).

  (** * Lemmas about the map elements *)
  Global Instance resource_map_elem_timeless k γ dq v : Timeless (k ↪[γ]{dq} v).
  Proof. unseal. apply _. Qed.
  Global Instance resource_map_elem_persistent k γ v : Persistent (k ↪[γ]□ v).
  Proof. unseal. apply _. Qed.
(*  Global Instance resource_map_elem_fractional k γ v : Fractional (λ q, k ↪[γ]{#q} v)%I.
  Proof. unseal. intros p q. rewrite -own_op juicy_view_frag_add //. Qed.
  Global Instance resource_map_elem_as_fractional k γ q v :
    AsFractional (k ↪[γ]{#q} v) (λ q, k ↪[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.*)
  Global Instance resource_map_elem_affine k γ v : Affine (k ↪[γ]□ v).
  Proof. unseal. apply _. Qed.
  Global Instance resource_map_elem_no_persistent k γ : Persistent (resource_map_elem_no γ k Share.bot).
  Proof. unseal. apply _. Qed.
  Global Instance resource_map_elem_no_affine k γ : Affine (resource_map_elem_no γ k Share.bot).
  Proof. unseal. apply _. Qed.
  Global Instance resource_map_elem_pure_persistent k γ v : Persistent (k ↪[γ]p v).
  Proof. unseal. apply _. Qed.
  Global Instance resource_map_elem_pure_affine k γ v : Affine (k ↪[γ]p v).
  Proof. unseal. apply _. Qed.

  Local Lemma resource_map_elems_unseal γ m dq (rsh : readable_dfrac dq) :
    ([∗ map] k ↦ v ∈ m, k ↪[γ]{dq} v) ==∗
    own γ ([^op map] k↦v ∈ m, ◯ {[k := Cinl (YES (V := leibnizO V) dq rsh (to_agree v))]}).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "? !>".
      iApply (big_sepM_mono with "[$]").
      intros; iIntros "(% & ?)".
      iApply (own_proper with "[$]").
      f_equiv.
      eapply @singletonM_proper; first apply _.
      f_equiv; done.
  Qed.

  Lemma resource_map_elem_valid k γ dq v : k ↪[γ]{dq} v -∗ ⌜✓ dq ∧ readable_dfrac dq⌝.
  Proof.
    unseal. iIntros "[% Helem]".
    iPoseProof (own_valid with "Helem") as "H".
    rewrite auth_frag_validI singleton_validI csum_validI shared_validI.
    iDestruct "H" as "(% & _)"; done.
  Qed.
  Lemma resource_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ readable_dfrac (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "[% H1] [% H2]".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    unshelve rewrite auth_frag_validI singleton_op singleton_validI csum_validI /= YES_op'.
    destruct (readable_dfrac_dec _); rewrite shared_validI; last done.
    rewrite to_agree_op_validI.
    iDestruct "H" as "(% & %)"; done.
  Qed.
  Lemma resource_map_elem_agree k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (resource_map_elem_valid_2 with "Helem1 Helem2") as %(_ & _ & ?).
    done.
  Qed.

  Global Instance resource_map_elem_combine_gives γ k v1 dq1 v2 dq2 :
    CombineSepGives (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ readable_dfrac (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (resource_map_elem_valid_2 with "H1 H2") as %[??].
    eauto.
  Qed.

  Lemma resource_map_elem_combine k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{dq1 ⋅ dq2} v1 ∧ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (resource_map_elem_valid_2 with "Hl1 Hl2") as %(? & Hv & ->); iSplit; last done.
    unseal. iDestruct "Hl1" as (?) "Hl1"; iDestruct "Hl2" as (?) "Hl2"; iExists Hv. iCombine "Hl1 Hl2" as "Hl". rewrite -own_op -auth_frag_op singleton_op -Cinl_op YES_op agree_idemp //.
  Qed.

  Global Instance resource_map_elem_combine_as k γ dq1 dq2 v1 v2 :
    CombineSepAs (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) (k ↪[γ]{dq1 ⋅ dq2} v1) | 60. 
    (* higher cost than the Fractional instance [combine_sep_fractional_bwd],
       which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (resource_map_elem_combine with "H1 H2") as "($ & _)".
  Qed.

  Lemma resource_map_elem_split k γ dq1 dq2 (rsh1 : readable_dfrac dq1) (rsh2 : readable_dfrac dq2) v :
    k ↪[γ]{dq1 ⋅ dq2} v ⊣⊢ k ↪[γ]{dq1} v ∗ k ↪[γ]{dq2} v.
  Proof.
    iSplit; last by iIntros "[A B]"; iCombine "A B" as "H".
    unseal. iIntros "[% ?]".
    rewrite bi.sep_exist_r; iExists rsh1.
    rewrite bi.sep_exist_l; iExists rsh2.
    rewrite -own_op -auth_frag_op singleton_op -Cinl_op YES_op agree_idemp //.
  Qed.

  Lemma resource_map_elem_no_valid k γ sh :
    resource_map_elem_no γ k sh -∗ ⌜~readable_share sh⌝.
  Proof.
    unseal. iIntros "[% H]"; done.
  Qed.

  Lemma resource_map_elem_no_elem_valid_2 k γ sh1 dq2 v2 :
    resource_map_elem_no γ k sh1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (DfracOwn (Share sh1) ⋅ dq2) ∧ readable_dfrac (DfracOwn (Share sh1) ⋅ dq2)⌝.
  Proof.
    unseal. iIntros "[% H1] [% H2]".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite -auth_frag_op singleton_op -Cinl_op NO_YES_op' auth_frag_validI singleton_validI csum_validI.
    destruct (readable_dfrac_dec _); rewrite shared_validI; last done.
    iDestruct "H" as "(% & _)"; done.
  Qed.

  Lemma resource_map_elem_no_valid_2 k γ sh1 sh2 :
    resource_map_elem_no γ k sh1 -∗ resource_map_elem_no γ k sh2 -∗ ⌜✓ (Share sh1 ⋅ Share sh2) ∧ ~readable_share' (Share sh1 ⋅ Share sh2)⌝.
  Proof.
    unseal. iIntros "[% H1] [% H2]".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite -auth_frag_op singleton_op -Cinl_op auth_frag_validI singleton_validI csum_validI shared_validI /=.
    iDestruct "H" as %Hv; iPureIntro.
    split; first done.
    apply share_valid2_joins in Hv as (? & ? & ? & [=] & [=] & Heq & ?); subst; rewrite Heq.
    by eapply join_unreadable_shares.
  Qed.

  Lemma resource_map_elem_no_elem_combine k γ sh1 dq2 v2 :
    resource_map_elem_no γ k sh1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{DfracOwn (Share sh1) ⋅ dq2} v2.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (resource_map_elem_no_elem_valid_2 with "Hl1 Hl2") as %[? Hv].
    unseal. iDestruct "Hl1" as (?) "Hl1"; iDestruct "Hl2" as (?) "Hl2"; iExists Hv. iCombine "Hl1 Hl2" as "Hl". rewrite -own_op -auth_frag_op singleton_op -Cinl_op NO_YES_op //.
  Qed.

  Lemma resource_map_elem_no_combine k γ sh1 sh2 :
    resource_map_elem_no γ k sh1 -∗ resource_map_elem_no γ k sh2 -∗ ∃ sh, ⌜sepalg.join sh1 sh2 sh⌝ ∧ resource_map_elem_no γ k sh.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (resource_map_elem_no_valid_2 with "Hl1 Hl2") as %[J Hv].
    unseal. iDestruct "Hl1" as "[% Hl1]"; iDestruct "Hl2" as "[% Hl2]"; iCombine "Hl1 Hl2" as "Hl".
    apply share_valid2_joins in J as (? & ? & sh & [=] & [=] & Heq & J); subst.
    iExists sh; iSplit; first done.
    rewrite -Heq; iExists Hv; rewrite -own_op -auth_frag_op singleton_op -Cinl_op.
    iApply (own_proper with "Hl"); f_equiv.
    eapply @singletonM_proper; first apply _.
    f_equiv; done.
  Qed.

  Lemma resource_map_elem_split_no k γ sh1 dq2 (rsh1 : ~readable_share sh1) (rsh2 : readable_dfrac dq2) v :
    k ↪[γ]{DfracOwn (Share sh1) ⋅ dq2} v ⊣⊢ resource_map_elem_no γ k sh1 ∗ k ↪[γ]{dq2} v.
  Proof.
    iSplit; last by iIntros "[A B]"; iApply (resource_map_elem_no_elem_combine with "A B").
    unseal. iIntros "[% ?]".
    rewrite bi.sep_exist_r; iExists rsh1.
    rewrite bi.sep_exist_l; iExists rsh2.
    rewrite -own_op -auth_frag_op singleton_op -Cinl_op NO_YES_op //.
  Qed.

  Lemma resource_map_elem_no_split k γ sh1 sh2 (rsh1 : ~readable_share sh1) (rsh2 : ~readable_share sh2) sh
    (J : sepalg.join sh1 sh2 sh) :
    resource_map_elem_no γ k sh ⊣⊢ resource_map_elem_no γ k sh1 ∗ resource_map_elem_no γ k sh2.
  Proof.
    iSplit.
    - unseal.
      assert (Share sh1 ⋅ Share sh2 = Share sh) as Heq by (apply share_op_join; eauto).
      rewrite -Heq; iIntros "(% & ?)".
      rewrite bi.sep_exist_r; iExists rsh1.
      rewrite bi.sep_exist_l; iExists rsh2.
      rewrite -own_op -auth_frag_op singleton_op -Cinl_op.
      iApply (own_proper with "[$]"); f_equiv.
      eapply @singletonM_proper; first apply _.
      f_equiv; done.
    - iIntros "[A B]"; iDestruct (resource_map_elem_no_combine with "A B") as (??) "?".
      eapply sepalg.join_eq in J as ->; eauto.
  Qed.

  Lemma resource_map_elem_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1} v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (resource_map_elem_valid_2 with "H1 H2") as %[??].
  Qed.
(*  Lemma resource_map_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 ↪[γ] v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply resource_map_elem_frac_ne. apply: exclusive_l. Qed.*)

  Lemma resource_map_elem_pure_agree k γ v1 v2 :
    k ↪[γ]p v1 -∗ k ↪[γ]p v2 -∗ ⌜v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite -auth_frag_op singleton_op -Cinr_op auth_frag_validI singleton_validI csum_validI to_agree_op_validI.
    iDestruct "H" as %?; done.
  Qed.

  Lemma resource_map_elem_no_pure_conflict k γ sh v : resource_map_elem_no γ k sh -∗ k ↪[γ]p v -∗ False.
  Proof.
    unseal. iIntros "(% & H1) H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite auth_frag_validI singleton_op singleton_validI csum_validI //.
  Qed.

(** Make an element read-only. This is a memory leak.
  Lemma resource_map_elem_persist k γ dq v :
    k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.
  Proof. unseal. iIntros "[% ?]"; iExists I. iApply (own_update with "[$]"). apply view_update_frag. Qed.

  Lemma resource_map_elem_bot k γ dq v :
    k ↪[γ]{dq} v ==∗ resource_map_elem_no γ k Share.bot.
  Proof. unseal. iIntros "[% ?]"; iExists bot_unreadable. iApply (own_update with "[$]"). apply juicy_view_frag_bot. Qed.

  Lemma resource_map_elem_no_bot k γ sh :
    resource_map_elem_no γ k sh ==∗ resource_map_elem_no γ k Share.bot.
  Proof. unseal. iIntros "[% ?]"; iExists bot_unreadable. iApply (own_update with "[$]"). apply juicy_view_frag_no_bot. Qed.*)

  (** * Lemmas about [resource_map_auth] *)
  Lemma resource_map_alloc_strong P (m : rmapUR K (leibnizO V)) :
    pred_infinite P → ✓ m →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ resource_map_auth γ 1 m ∗ own γ (◯ m).
  Proof.
    unseal. intros.
    setoid_rewrite <- own_op.
    iApply own_alloc_strong.
    apply auth_both_valid_2; done.
  Qed.
  Lemma resource_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ resource_map_auth γ 1 ∅.
  Proof.
    unseal. intros.
    iApply own_alloc_strong.
    by apply auth_auth_valid.
  Qed.
  Lemma resource_map_alloc (m : rmapUR K (leibnizO V)) :
    ✓ m →
    ⊢ |==> ∃ γ, resource_map_auth γ 1 m ∗ own γ (◯ m).
  Proof.
    intros; iMod (resource_map_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma resource_map_alloc_empty :
    ⊢ |==> ∃ γ, resource_map_auth γ 1 ∅.
  Proof.
    iMod (resource_map_alloc_strong_empty (λ _, True)) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.

  Global Instance resource_map_auth_timeless γ q m : Timeless (resource_map_auth γ q m).
  Proof. unseal. apply _. Qed.
(*  Global Instance resource_map_auth_fractional γ m : Fractional (λ q, resource_map_auth γ q m)%I.
  Proof. intros p q. unseal. rewrite -own_op -juicy_view_auth_dfrac_op //. Qed.
  Global Instance resource_map_auth_as_fractional γ q m :
    AsFractional (resource_map_auth γ q m) (λ q, resource_map_auth γ q m)%I q.
  Proof. split; first done. apply _. Qed.*)

  Lemma resource_map_auth_valid γ q m : resource_map_auth γ q m -∗ ⌜✓ q ∧ ✓ m⌝.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as "H".
    rewrite auth_auth_dfrac_validI; iDestruct "H" as "(% & %)"; done.
  Qed.
  Lemma resource_map_auth_valid_2 γ q1 q2 m1 m2 :
    resource_map_auth γ q1 m1 -∗ resource_map_auth γ q2 m2 -∗ ⌜✓ (q1 ⋅ q2) ∧ m1 ≡ m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as "H".
    rewrite auth_auth_dfrac_op_validI.
    iDestruct "H" as "(% & % & _)"; done.
  Qed.
  Lemma resource_map_auth_agree γ q1 q2 m1 m2 :
    resource_map_auth γ q1 m1 -∗ resource_map_auth γ q2 m2 -∗ m1 ≡ m2.
  Proof.
    iIntros "H1 H2".
    iDestruct (resource_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [resource_map_auth] with the elements *)
  Lemma resource_map_lookup {γ q m k dq v} :
    resource_map_auth γ q m -∗ k ↪[γ]{dq} v -∗ ⌜∃ dq', ∃ rsh : readable_dfrac dq', ✓ dq' ∧ dq ≼ dq' ∧
      m !! k ≡ Some (Cinl (YES (V := leibnizO V) dq' rsh (to_agree v)))⌝.
  Proof.
    unseal. iIntros "Hauth [% Hel]".
    iDestruct (own_valid_2 with "Hauth Hel") as "H".
    rewrite auth_both_dfrac_validI.
    iDestruct "H" as (? (m' & Hm)) "Hv".
    rewrite gmap_validI; iSpecialize ("Hv" $! k).
    specialize (Hm k).
    rewrite lookup_op lookup_singleton Some_op_opM in Hm; inversion Hm as [x ? Hk Heq|]; subst.
    rewrite ouPred.option_validI -Heq csum_validI.
    clear Hm Heq; inversion Hk as [?? Ha Hb Hl | |]; last done; last by (destruct (_ !! _) as [[| |]|]).
    subst; rewrite shared_validI.
    destruct (_ !! _) as [[o| |]|]; inv Hl.
    - pose proof (shared_op_alt _ (YES (V := leibnizO V) dq rsh (to_agree v)) o) as Hop.
      simpl in Hop; destruct (readable_dfrac_dec _).
      + destruct Hop as (? & Hv & Hop); rewrite Hop in Ha.
        destruct a; last done.
        iDestruct "Hv" as "(% & %Hvv)".
        iPureIntro; exists dq0, rsh0.
        rewrite Some_op_opM in Hv; inv Hv.
        destruct Ha as [-> Hv]; rewrite Hv in Hvv |- *.
        split; first done; split; first by eexists.
        f_equiv; f_equiv; split; first done.
        destruct (val_of o); last done.
        apply agree_op_inv in Hvv as <-.
        rewrite /= agree_idemp //.
      + destruct (dfrac_error _); last by destruct Hop as (? & ? & ? & ? & ? & ?).
        rewrite Hop in Ha; destruct a; inv Ha; done.
    - destruct a; last done.
      destruct Ha as [-> Hv].
      iDestruct "Hv" as "(% & _)".
      iPureIntro; exists dq, rsh; split; first done; split; first done.
      f_equiv; f_equiv; split; done.
  Qed.

  Global Instance resource_map_lookup_combine_gives_1 {γ q m k dq v} :
    CombineSepGives (resource_map_auth γ q m) (k ↪[γ]{dq} v) ⌜∃ dq', ∃ rsh : readable_dfrac dq', ✓ dq' ∧ dq ≼ dq' ∧
      m !! k ≡ Some (Cinl (YES (V := leibnizO V) dq' rsh (to_agree v)))⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (resource_map_lookup with "H1 H2") as %?. eauto.
  Qed.

  Global Instance resource_map_lookup_combine_gives_2 {γ q m k dq v} :
    CombineSepGives (k ↪[γ]{dq} v) (resource_map_auth γ q m) ⌜∃ dq', ∃ rsh : readable_dfrac dq', ✓ dq' ∧ dq ≼ dq' ∧
      m !! k ≡ Some (Cinl (YES (V := leibnizO V) dq' rsh (to_agree v)))⌝.
  Proof.
    rewrite /CombineSepGives comm. apply resource_map_lookup_combine_gives_1.
  Qed.

  Lemma resource_map_no_lookup {γ q m k sh} :
    resource_map_auth γ q m -∗ resource_map_elem_no γ k sh -∗ ⌜∃ s, ✓ s ∧ m !! k = Some (Cinl s) ∧ DfracOwn (Share sh) ≼ dfrac_of s⌝.
  Proof.
    unseal. iIntros "Hauth [% Hel]".
    iDestruct (own_valid_2 with "Hauth Hel") as "H".
    rewrite auth_both_dfrac_validI.
    iDestruct "H" as (? (m' & Hm)) "Hv".
    rewrite gmap_validI; iSpecialize ("Hv" $! k).
    specialize (Hm k).
    rewrite lookup_op lookup_singleton Some_op_opM in Hm; inversion Hm as [x ? Hk Heq|]; subst.
    rewrite ouPred.option_validI -Heq csum_validI.
    clear Hm Heq; inversion Hk as [?? Ha Hb Hl | |]; last done; last by (destruct (_ !! _) as [[| |]|]).
    iDestruct "Hv" as %Hvalid.
    iPureIntro; eexists; split; first done; split; first done.
    erewrite (dfrac_of_ne _ O); last by apply equiv_dist.
    destruct (m' !! k) as [[| |]|] eqn: Hk'; rewrite Hk' in Hl; inv Hl; try done.
    rewrite Ha in Hvalid; apply shared_valid in Hvalid as [Hd _].
    rewrite dfrac_of_op' in Hd |- *.
    destruct (dfrac_error _); first done.
    by eexists.
  Qed.

  Lemma resource_map_pure_lookup {γ q m k v} :
    resource_map_auth γ q m -∗ k ↪[γ]p v -∗ ⌜m !! k ≡ Some (Cinr (to_agree (v : leibnizO V)))⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as "H".
    rewrite auth_both_dfrac_validI.
    iDestruct "H" as (? (m' & Hm)) "Hv".
    rewrite gmap_validI; iSpecialize ("Hv" $! k).
    specialize (Hm k).
    rewrite lookup_op lookup_singleton Some_op_opM in Hm; inversion Hm as [x ? Hk Heq|]; subst.
    rewrite ouPred.option_validI -Heq csum_validI.
    clear Hm Heq; inversion Hk as [| ?? Ha Hb Hl |]; last done; first by (destruct (_ !! _) as [[| |]|]).
    subst.
    rewrite Ha.
    destruct (_ !! _) as [[| o|]|]; inv Hl; try done.
    rewrite agree_validI; iDestruct "Hv" as %<-.
    rewrite agree_idemp //.
  Qed.

  Lemma readable_Tsh : readable_share Tsh.
  Proof. auto. Qed.

  Lemma resource_map_insert {γ m} k v :
    m !! k = None →
    resource_map_auth γ 1 m ==∗ resource_map_auth γ 1 (<[k := Cinl (YES (V := leibnizO V) (DfracOwn (Share Tsh)) readable_Tsh (to_agree v))]> m) ∗ k ↪[γ] v.
  Proof.
    unseal. intros ?.
    iIntros "H"; rewrite bi.sep_exist_l.
    iExists readable_Tsh.
    rewrite -own_op.
    iApply (own_update with "H").
    apply auth_update_alloc, alloc_singleton_local_update; done.
  Qed.
  Lemma resource_map_insert_persist {γ m} k v :
    m !! k = None →
    resource_map_auth γ 1 m ==∗ resource_map_auth γ 1 (<[k := Cinl (YES (V := leibnizO V) DfracDiscarded I (to_agree v))]> m) ∗ k ↪[γ]□ v.
  Proof.
    unseal. intros ?.
    iIntros "H"; rewrite bi.sep_exist_l.
    iExists I.
    rewrite -own_op.
    iApply (own_update with "H").
    apply auth_update_alloc, alloc_singleton_local_update; try done.
    split; try done; apply dfrac_valid_discarded.
  Qed.

  Lemma resource_map_delete {γ m k v} :
    resource_map_auth γ 1 m -∗ k ↪[γ] v ==∗ resource_map_auth γ 1 (<[k := Cinl ε]>m).
  Proof.
    iIntros "Hm H".
    iDestruct (resource_map_lookup with "Hm H") as %(? & ? & Hv & Hd & Hk).
    unseal.
    iDestruct "H" as (?) "H".
    iPoseProof (own_update_2 with "Hm H") as ">H".
    { apply auth_update, singleton_local_update_any.
      intros ? Hk'; rewrite Hk' in Hk; inversion Hk as [?? Heq|].
      subst; inversion Heq as [a ? Heq' | |]; destruct a; last done.
      destruct Heq' as [-> ->]; subst.
      destruct Hd as (? & Hd); rewrite Hd in Hv; apply dfrac_full_exclusive in Hv as ->.
      rewrite right_id in Hd; inv Hd.
      apply csum_local_update_l.
      rewrite -{1}(uora_unit_right_id (YES _ _ _)).
      assert (YES (V := leibnizO V) (DfracOwn (Share Tsh)) rsh0 (to_agree v) ≡ YES (V := leibnizO V) (DfracOwn (Share Tsh)) rsh (to_agree v)) as -> by done.
      apply cancel_local_update_unit, _. }
    rewrite own_op; iDestruct "H" as "($ & _)"; done.
  Qed.

  Lemma resource_map_update {γ m k sh v} (Hsh : writable0_share sh) w :
    resource_map_auth γ 1 m -∗ k ↪[γ]{#sh} v ==∗ ∃ dq' rsh', ⌜✓ dq' ∧ DfracOwn (Share sh) ≼ dq' ∧
      m !! k ≡ Some (Cinl (YES (V := leibnizO V) dq' rsh' (to_agree v)))⌝ ∧
    resource_map_auth γ 1 (<[k := Cinl (YES dq' rsh' (to_agree w))]> m) ∗ k ↪[γ]{#sh} w.
  Proof.
    iIntros "Hm H".
    iDestruct (resource_map_lookup with "Hm H") as %(dq' & rsh' & Hv & Hd & Hk).
    unseal.
    iDestruct "H" as "(% & H)".
    iExists dq', rsh'.
    rewrite bi.pure_True // bi.True_and.
    rewrite bi.sep_exist_l; iExists rsh.
    rewrite -own_op; iApply (own_update_2 with "Hm H").
    apply auth_update, singleton_local_update_any.
    intros ? Hk'; rewrite Hk' in Hk; inversion Hk as [?? Heq|].
    subst; inversion Heq as [a ? Heq' | |]; destruct a; last done.
    destruct Heq' as [-> ->]; subst.
    apply csum_local_update_l.
    intros ??; simpl; intros Hv' Hc'.
    split; first done.
    destruct mz; last by destruct Hc' as [-> ?].
    rewrite !shared_dist' /= !dfrac_of_op' !val_of_op' in Hc' |- *.
    destruct Hc' as [-> Hval'].
    destruct (dfrac_error _) eqn: Herr; try done.
    destruct c; try done.
    simpl in *.
    rewrite comm in Hv; apply dfrac_valid_own_readable in Hv as (? & [=] & ?); subst; done.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma resource_map_lookup_big {γ q m} dq m0 :
    resource_map_auth γ q m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ]{dq} v) -∗
    ⌜map_Forall (fun k v => ∃ dq', ∃ rsh : readable_dfrac dq', ✓ dq' ∧ dq ≼ dq' ∧
            m !! k ≡ Some (Cinl (YES (V := leibnizO V) dq' rsh (to_agree v)))) m0⌝.
  Proof.
    iIntros "Hauth Hfrag" (k v Hk).
    rewrite big_sepM_lookup_acc; last done.
    iDestruct "Hfrag" as "[Hfrag ?]".
    iApply (resource_map_lookup with "Hauth Hfrag").
  Qed.

  Lemma big_sepM_exist : ∀ {PROP : bi} {A} (P : K -> V -> A -> PROP) m, (∃ y, [∗ map] k↦x ∈ m, P k x y) ⊢ [∗ map] k↦x ∈ m, ∃ y, P k x y.
  Proof.
    intros; iIntros "(% & H)".
    iApply (big_sepM_mono with "H"); eauto.
  Qed.

  Lemma resource_map_insert_big {γ m} m' :
    dom m' ## dom m →
    resource_map_auth γ 1 m ==∗
    resource_map_auth γ 1 (((λ v, Cinl (YES (V := leibnizO V) (DfracOwn (Share Tsh)) readable_Tsh (to_agree v))) <$> m') ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ] v).
  Proof.
    revert m; induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint; intros ? Hdisj.
    { rewrite fmap_empty big_opM_empty.
      unseal. rewrite own_proper; first by iIntros "$".
      f_equiv; intros i; rewrite lookup_union lookup_empty option_union_left_id //. }
  rewrite dom_insert in Hdisj; apply disjoint_union_l in Hdisj as [?%disjoint_singleton_l ?].
  rewrite big_sepM_insert // IH //.
  iIntros ">(H & $)".
  rewrite fmap_insert -insert_union_l.
  iApply (resource_map_insert with "H").
  rewrite lookup_union lookup_fmap H1 /=.
  eapply @not_elem_of_dom_1 in H2 as ->; last apply _; done.
  Qed.
  Lemma resource_map_insert_persist_big {γ m} m' :
    dom m' ## dom m →
    resource_map_auth γ 1 m ==∗
    resource_map_auth γ 1 (((λ v, Cinl (YES (V := leibnizO V) DfracDiscarded I (to_agree v))) <$> m') ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]□ v).
  Proof.
    induction m' as [|k v m' ? IH] using map_ind; decompose_map_disjoint; intros Hdisj.
    { rewrite fmap_empty big_opM_empty.
      unseal. rewrite own_proper; first by iIntros "$".
      f_equiv; intros i; rewrite lookup_union lookup_empty option_union_left_id //. }
    rewrite dom_insert in Hdisj; apply disjoint_union_l in Hdisj as [?%disjoint_singleton_l ?].
    rewrite big_sepM_insert // IH //.
    iIntros ">(H & $)".
    rewrite fmap_insert -insert_union_l.
    iApply (resource_map_insert_persist with "H").
    rewrite lookup_union lookup_fmap H1 /=.
    eapply @not_elem_of_dom_1 in H2 as ->; last apply _; done.
  Qed.

  Lemma resource_map_delete_big {γ m} m0 :
    resource_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    resource_map_auth γ 1 (((λ _, Cinl ε) <$> m0) ∪ m).
  Proof.
    induction m0 as [|k v m' ? IH] using map_ind.
    { rewrite fmap_empty big_opM_empty !left_id; auto. }
    rewrite big_sepM_insert //.
    iIntros "Hm (Hk & Hrest)"; iMod (IH with "Hm Hrest") as "Hm".
    iMod (resource_map_delete with "Hm Hk").
    rewrite fmap_insert -insert_union_l //.
  Qed.

  Lemma resource_map_update_big {γ m} sh (Hsh : writable0_share sh) m0 m1 :
    dom m0 = dom m1 →
    resource_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ]{#sh} v) ==∗
    resource_map_auth γ 1 (union(Union := map_union) (map_imap (λ k v, match m !! k with
      | Some (Cinl (YES dq' rsh _)) => Some (Cinl (YES (V := leibnizO V) dq' rsh (to_agree v)))
      | _ => Some CsumBot end) m1) m) ∗
        [∗ map] k↦v ∈ m1, k ↪[γ]{#sh} v.
  Proof.
    revert m1; induction m0 as [|k v m' ? IH] using map_ind; intros ? Hdom.
    { rewrite dom_empty_L in Hdom.
      symmetry in Hdom; apply dom_empty_inv_L in Hdom as ->.
      rewrite !big_opM_empty !left_id; auto. }
    rewrite dom_insert_L in Hdom.
    rewrite big_sepM_insert //.
    iIntros "Hm (Hk & Hrest)"; iMod (IH (delete k m1) with "Hm Hrest") as "(Hm & Hrest)".
    { rewrite dom_delete_L -Hdom difference_union_distr_l_L difference_diag_L left_id_L difference_disjoint_L //.
      apply disjoint_singleton_r, not_elem_of_dom_2; done. }
    assert (k ∈ dom m1) as (v1 & Hm1)%elem_of_dom by set_solver.
    iMod (resource_map_update with "Hm Hk") as (?? (? & ? & Hmk)) "(Hm & Hk)".
    iCombine "Hk Hrest" as "Hm1".
    rewrite -(big_sepM_insert_delete (λ k v, k ↪[γ]{#sh} v))%I insert_id //; iFrame.
    rewrite -{2}(insert_delete _ _ _ Hm1) map_imap_insert.
    rewrite lookup_union map_lookup_imap lookup_delete left_id in Hmk.
    inversion Hmk as [?? Heq Hk|]; subst; rewrite -Hk.
    inversion Heq as [[|] ? Heq' | |]; inv Heq'.
    iIntros "!>"; iStopProof; apply bi.equiv_entails_1_1.
    unseal; f_equiv; f_equiv.
    rewrite insert_union_l; f_equiv; f_equiv; f_equiv; done.
  Qed.

  Definition elem_of_agree {A} (x : agree A) : { a | a ∈ agree_car x}.
  Proof. destruct x as [[|a ?] ?]; [done | exists a; apply elem_of_cons; auto]. Qed.

  Theorem resource_map_set γ σ (Hvalid : ✓ σ) :
    resource_map_auth γ 1 ∅ ==∗ resource_map_auth γ 1 σ ∗
    ([∗ map] l ↦ x ∈ σ, match x with
                        | Cinl (YES dq _ v) => l ↪[γ]{dq} (proj1_sig (elem_of_agree v))
                        | Cinl (NO (Share sh) _) => resource_map_elem_no γ l sh
                        | Cinr v => l ↪[γ]p (proj1_sig (elem_of_agree v))
                        | _ => False
                        end).
  Proof.
    unseal. iIntros "H".
    iMod (own_update with "H") as "($ & ?)".
    { apply auth_update_alloc.
      intros ??; simpl.
      eapply cmra_valid_validN in Hvalid.
      destruct mz; simpl; last done.
      rewrite left_id; intros _ <-; rewrite right_id //. }
    rewrite -{1}(big_opM_singletons σ) big_opM_auth_frag.
    iPoseProof (big_opM_own_1 with "[-]") as "?"; first done.
    iApply big_sepM_mono; last done; intros ?? Hk.
    specialize (Hvalid k); rewrite Hk in Hvalid.
    destruct x as [[|] | |]; last done.
    - iIntros "H"; iExists rsh.
      iApply (own_proper with "H").
      f_equiv; eapply @singletonM_proper; first apply _; f_equiv.
      split; first done.
      destruct Hvalid as [_ Hvalid].
      destruct (elem_of_agree v); simpl.
      intros n.
      specialize (Hvalid n); rewrite agree_validN_def in Hvalid.
      split=> b /=; setoid_rewrite elem_of_list_singleton; eauto.
    - destruct sh; try done.
      iIntros "?"; iExists rsh; done.
    - rewrite own_proper //.
      f_equiv; eapply @singletonM_proper; first apply _; f_equiv.
      destruct (elem_of_agree _); simpl.
      intros n.
      specialize (Hvalid n); rewrite agree_validN_def in Hvalid.
      split=> b /=; setoid_rewrite elem_of_list_singleton; eauto.
  Qed.

End lemmas.
