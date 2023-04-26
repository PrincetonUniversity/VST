(* modified from iris.base_logic.lib.resource_map *)

(** A "ghost map" (or "ghost heap") with a proposition controlling authoritative
ownership of the entire heap, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements. *)
From iris.proofmode Require Import proofmode.
From iris_ora.logic Require Export logic own.
From VST.veric Require Export shares share_alg.
From VST.veric Require Import view juicy_view.
From iris.prelude Require Import options.
Export Address.

Class resource_mapG Σ (V : Type) `{resource_ops (leibnizO V)} := GhostMapG {
  resource_map_inG : inG Σ (juicy_viewR (leibnizO V));
}.
Local Existing Instance resource_map_inG.

Definition resource_mapΣ (V : Type) `{resource_ops (leibnizO V)} : gFunctors :=
  #[ GFunctor (juicy_viewR (leibnizO V)) ].

Global Instance subG_resource_mapΣ Σ (V : Type) `{resource_ops (leibnizO V)} :
  subG (resource_mapΣ V) Σ → resource_mapG Σ V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{resource_mapG Σ V}.

  Local Definition resource_map_auth_def
      (γ : gname) (q : share) (m : mem) : iProp Σ :=
    own γ (juicy_view_auth (V:=leibnizO V) (DfracOwn q) m).
  Local Definition resource_map_auth_aux : seal (@resource_map_auth_def).
  Proof. by eexists. Qed.
  Definition resource_map_auth := resource_map_auth_aux.(unseal).
  Local Definition resource_map_auth_unseal :
    @resource_map_auth = @resource_map_auth_def := resource_map_auth_aux.(seal_eq).

  Local Definition resource_map_elem_def
      (γ : gname) (k : address) (dq : dfrac) (v : V) : iProp Σ :=
    ∃ rsh, own γ (juicy_view_frag (V:=leibnizO V) k dq rsh v).
  Local Definition resource_map_elem_aux : seal (@resource_map_elem_def).
  Proof. by eexists. Qed.
  Definition resource_map_elem := resource_map_elem_aux.(unseal).
  Local Definition resource_map_elem_unseal :
    @resource_map_elem = @resource_map_elem_def := resource_map_elem_aux.(seal_eq).

  Local Definition resource_map_elem_no_def
      (γ : gname) (k : address) (sh : share) : iProp Σ :=
    ∃ rsh, own γ (juicy_view_frag_no (V:=leibnizO V) k sh rsh).
  Local Definition resource_map_elem_no_aux : seal (@resource_map_elem_no_def).
  Proof. by eexists. Qed.
  Definition resource_map_elem_no := resource_map_elem_no_aux.(unseal).
  Local Definition resource_map_elem_no_unseal :
    @resource_map_elem_no = @resource_map_elem_no_def := resource_map_elem_no_aux.(seal_eq).

  Local Definition resource_map_elem_pure_def
      (γ : gname) k v : iProp Σ :=
    own γ (juicy_view_frag_pure (V:=leibnizO V) k v).
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
  Context `{resource_mapG Σ V}.
  Implicit Types (k : address) (v : V) (dq : dfrac) (q : shareR).

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
  Global Instance resource_map_elem_pure_persistent k γ v : Persistent (k ↪[γ]p v).
  Proof. unseal. apply _. Qed.
  Global Instance resource_map_elem_pure_affine k γ v : Affine (k ↪[γ]p v).
  Proof. unseal. apply _. Qed.

  Local Lemma resource_map_elems_unseal γ k m dq (rsh : readable_dfrac dq) :
    ([∗ list] i↦v ∈ m, adr_add k (Z.of_nat i) ↪[γ]{dq} v) ==∗
    own γ ([^op list] i↦v ∈ m, juicy_view_frag (V:=leibnizO V) (adr_add k (Z.of_nat i)) dq rsh v).
  Proof.
    unseal. destruct (decide (m = [])) as [->|Hne].
    - rewrite !big_opL_nil. iIntros "_". iApply own_unit.
    - rewrite big_opL_own //. iIntros "?".
      iApply (big_opL_proper with "[$]"); intros.
      iSplit; first eauto.
      iIntros "(% & ?)"; by rewrite juicy_view_frag_irrel.
  Qed.

  Lemma resource_map_elem_valid k γ dq v : k ↪[γ]{dq} v -∗ ⌜✓ dq ∧ readable_dfrac dq⌝.
  Proof.
    unseal. iIntros "[% Helem]".
    iDestruct (own_valid with "Helem") as %?%juicy_view_frag_valid.
    done.
  Qed.
  Lemma resource_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ readable_dfrac (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "[% H1] [% H2]".
    iDestruct (own_valid_2 with "H1 H2") as %[Hv ?]%juicy_view_frag_op_valid.
    iSplit; first done.
    apply dfrac_op_readable' in Hv; auto.
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
    unseal. iDestruct "Hl1" as (?) "Hl1"; iDestruct "Hl2" as (?) "Hl2"; iExists Hv. iCombine "Hl1 Hl2" as "Hl". rewrite -own_op -juicy_view_frag_op //.
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
    unseal. iIntros "[% ?]"; rewrite juicy_view_frag_op own_op.
    rewrite bi.sep_exist_r; iExists rsh1.
    rewrite bi.sep_exist_l; iExists rsh2.
    done.
  Qed.

  Lemma resource_map_elem_no_valid k γ sh :
    resource_map_elem_no γ k sh -∗ ⌜✓ sh ∧ ~readable_share sh⌝.
  Proof.
    unseal. iIntros "[% H]".
    iDestruct (own_valid with "H") as %Hv%juicy_view_frag_no_valid.
    done.
  Qed.

  Lemma resource_map_elem_no_elem_valid_2 k γ sh1 dq2 v2 :
    resource_map_elem_no γ k sh1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (DfracOwn sh1 ⋅ dq2) ∧ readable_dfrac (DfracOwn sh1 ⋅ dq2)⌝.
  Proof.
    unseal. iIntros "[% H1] [% H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hv%juicy_view_frag_no_frag_op_valid.
    iSplit; first done.
    apply dfrac_op_readable' in Hv; auto.
  Qed.

  Lemma resource_map_elem_no_valid_2 k γ sh1 sh2 :
    resource_map_elem_no γ k sh1 -∗ resource_map_elem_no γ k sh2 -∗ ⌜✓ (sh1 ⋅ sh2) ∧ ~readable_share (sh1 ⋅ sh2)⌝.
  Proof.
    unseal. iIntros "[% H1] [% H2]".
    iDestruct (own_valid_2 with "H1 H2") as %Hv%juicy_view_frag_no_op_valid.
    iSplit; first done.
    apply share_valid2_joins in Hv as (? & ? & ?).
    iPureIntro; by eapply join_unreadable_shares.
  Qed.

  Lemma resource_map_elem_no_elem_combine k γ sh1 dq2 v2 :
    resource_map_elem_no γ k sh1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{DfracOwn sh1 ⋅ dq2} v2.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (resource_map_elem_no_elem_valid_2 with "Hl1 Hl2") as %[? Hv].
    unseal. iDestruct "Hl1" as (?) "Hl1"; iDestruct "Hl2" as (?) "Hl2"; iExists Hv. iCombine "Hl1 Hl2" as "Hl". rewrite -own_op -juicy_view_frag_no_frag_op //.
  Qed.

  Lemma resource_map_elem_no_combine k γ sh1 sh2 :
    resource_map_elem_no γ k sh1 -∗ resource_map_elem_no γ k sh2 -∗ resource_map_elem_no γ k (sh1 ⋅ sh2).
  Proof.
    iIntros "Hl1 Hl2". iDestruct (resource_map_elem_no_valid_2 with "Hl1 Hl2") as %[? Hv].
    unseal. iDestruct "Hl1" as "[% Hl1]"; iDestruct "Hl2" as "[% Hl2]"; iCombine "Hl1 Hl2" as "Hl". iExists Hv; rewrite -own_op -juicy_view_frag_no_op //.
  Qed.

  Lemma resource_map_elem_split_no k γ sh1 dq2 (rsh1 : ~readable_share sh1) (rsh2 : readable_dfrac dq2) v :
    k ↪[γ]{DfracOwn sh1 ⋅ dq2} v ⊣⊢ resource_map_elem_no γ k sh1 ∗ k ↪[γ]{dq2} v.
  Proof.
    iSplit; last by iIntros "[A B]"; iApply (resource_map_elem_no_elem_combine with "A B").
    unseal. iIntros "[% ?]"; rewrite juicy_view_frag_no_frag_op own_op.
    rewrite bi.sep_exist_r; iExists rsh1.
    rewrite bi.sep_exist_l; iExists rsh2.
    done.
  Qed.

  Lemma resource_map_elem_no_split k γ sh1 sh2 (rsh1 : ~readable_share sh1) (rsh2 : ~readable_share sh2) :
    resource_map_elem_no γ k (sh1 ⋅ sh2) ⊣⊢ resource_map_elem_no γ k sh1 ∗ resource_map_elem_no γ k sh2.
  Proof.
    iSplit; last by iIntros "[A B]"; iApply (resource_map_elem_no_combine with "A B").
    unseal. iIntros "[% ?]"; rewrite juicy_view_frag_no_op own_op.
    rewrite bi.sep_exist_r; iExists rsh1.
    rewrite bi.sep_exist_l; iExists rsh2.
    done.
  Qed.

  Lemma resource_map_elem_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1} v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (resource_map_elem_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma resource_map_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 ↪[γ] v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply resource_map_elem_frac_ne. apply: exclusive_l. Qed.

  Lemma resource_map_elem_pure_agree k γ v1 v2 :
    k ↪[γ]p v1 -∗ k ↪[γ]p v2 -∗ ⌜v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%juicy_view_frag_pure_op_valid.
    done.
  Qed.

  (** Make an element read-only. *)
  Lemma resource_map_elem_persist k γ dq v :
    k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.
  Proof. unseal. iIntros "[% ?]"; iExists I. iApply (own_update with "[$]"). apply juicy_view_frag_persist. Qed.

  (** * Lemmas about [resource_map_auth] *)
  Lemma resource_map_alloc_strong P m (f : juicy_view.juicy_view_fragUR (leibnizO V)) :
    pred_infinite P → ✓ f → (∀ loc, coherent_loc m loc (resource_at f loc)) →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ resource_map_auth γ Tsh m ∗ own γ (◯V f).
  Proof.
    unseal. intros.
    setoid_rewrite <- own_op.
    iApply own_alloc_strong.
    split; first done.
    intros; eexists; split; first done.
    split; simpl.
    - by rewrite left_id; apply cmra_valid_validN.
    - intros; rewrite /resource_at lookup_op lookup_empty op_None_left_id; eauto.
  Qed.
  Lemma resource_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ resource_map_auth γ Tsh Mem.empty.
  Proof.
    unseal. intros.
    iApply own_alloc_strong.
    by apply juicy_view_auth_dfrac_valid.
  Qed.
  Lemma resource_map_alloc m (f : juicy_view.juicy_view_fragUR (leibnizO V)):
    ✓ f → (∀ loc, coherent_loc m loc (resource_at f loc)) →
    ⊢ |==> ∃ γ, resource_map_auth γ Tsh m ∗ own γ (◯V f).
  Proof.
    intros; iMod (resource_map_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma resource_map_alloc_empty :
    ⊢ |==> ∃ γ, resource_map_auth γ Tsh Mem.empty.
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

  Lemma resource_map_auth_valid γ q m : resource_map_auth γ q m -∗ ⌜q ≠ Share.bot⌝.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%juicy_view_auth_dfrac_valid.
    done.
  Qed.
  Lemma resource_map_auth_valid_2 γ q1 q2 m1 m2 :
    resource_map_auth γ q1 m1 -∗ resource_map_auth γ q2 m2 -∗ ⌜q1 ⋅ q2 ≠ Share.bot ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%juicy_view_auth_dfrac_op_valid.
    done.
  Qed.
  Lemma resource_map_auth_agree γ q1 q2 m1 m2 :
    resource_map_auth γ q1 m1 -∗ resource_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (resource_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [resource_map_auth] with the elements *)
  Lemma resource_map_lookup {γ q m k dq v} :
    resource_map_auth γ q m -∗ k ↪[γ]{dq} v -∗ ⌜✓ dq ∧ readable_dfrac dq ∧ coherent_loc m k (Some (dq, Some v))⌝.
  Proof.
    unseal. iIntros "Hauth [% Hel]".
    iDestruct (own_valid_2 with "Hauth Hel") as %[?[??]]%juicy_view_both_dfrac_valid.
    eauto.
  Qed.

  Global Instance resource_map_lookup_combine_gives_1 {γ q m k dq v} :
    CombineSepGives (resource_map_auth γ q m) (k ↪[γ]{dq} v) ⌜✓ dq ∧ readable_dfrac dq ∧ coherent_loc m k (Some (dq, Some v))⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (resource_map_lookup with "H1 H2") as %?. eauto.
  Qed.

  Global Instance resource_map_lookup_combine_gives_2 {γ q m k dq v} :
    CombineSepGives (k ↪[γ]{dq} v) (resource_map_auth γ q m) ⌜✓ dq ∧ readable_dfrac dq ∧ coherent_loc m k (Some (dq, Some v))⌝.
  Proof.
    rewrite /CombineSepGives comm. apply resource_map_lookup_combine_gives_1.
  Qed.

  Lemma resource_map_no_lookup {γ q m k sh} :
    resource_map_auth γ q m -∗ resource_map_elem_no γ k sh -∗ ⌜✓ sh ∧ ~readable_share sh ∧ coherent_loc m k (Some (DfracOwn sh, None))⌝.
  Proof.
    unseal. iIntros "Hauth [% Hel]".
    iDestruct (own_valid_2 with "Hauth Hel") as %[?[??]]%juicy_view_both_no_dfrac_valid.
    eauto.
  Qed.

  Lemma resource_map_pure_lookup {γ q m k v} :
    resource_map_auth γ q m -∗ k ↪[γ]p v -∗ ⌜coherent_loc m k (Some (DfracOwn Share.Lsh, Some v))⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as %[??]%juicy_view_both_pure_dfrac_valid.
    eauto.
  Qed.

  Lemma resource_map_mem_alloc {γ m} lo hi m' b v (Halloc : Mem.alloc m lo hi = (m', b)) (Hundef : memval_of v = Some Undef) :
    resource_map_auth γ Tsh m ==∗ resource_map_auth γ Tsh m' ∗ ([∗ list] i↦v ∈ replicate (Z.to_nat (hi - lo)) v, adr_add (b, lo) (Z.of_nat i) ↪[γ]{DfracOwn Tsh} v).
  Proof.
    unseal.
    rewrite (big_sepL_proper _ (λ i v, own γ (juicy_view_frag(V := leibnizO V) (adr_add (b, lo) i) (DfracOwn Tsh) readable_Tsh v)) _).
    2: { intros; iSplit; last eauto. iIntros "[% ?]"; by rewrite juicy_view_frag_irrel. }
    rewrite -big_opL_own_1 -own_op.
    iApply own_update. apply: juicy_view_alloc; done.
  Qed.
  Lemma resource_map_alloc_persist {γ m} lo hi m' b v (Halloc : Mem.alloc m lo hi = (m', b)) (Hundef : memval_of v = Some Undef) :
    resource_map_auth γ Tsh m ==∗ resource_map_auth γ Tsh m' ∗ ([∗ list] i↦v ∈ replicate (Z.to_nat (hi - lo)) v, adr_add (b, lo) (Z.of_nat i) ↪[γ]□ v).
  Proof.
    rewrite resource_map_mem_alloc; [|done..].
    iIntros ">[$ ?]".
    iApply big_sepL_bupd.
    iApply (big_sepL_mono with "[$]").
    intros; apply resource_map_elem_persist.
  Qed.

  Lemma resource_map_free {γ m k vl} hi m' (Hfree : Mem.free m k.1 k.2 hi = Some m') (Hlen : length vl = Z.to_nat (hi - k.2)) :
    resource_map_auth γ Tsh m -∗ ([∗ list] i↦v ∈ vl, adr_add k (Z.of_nat i) ↪[γ]{DfracOwn Tsh} v) ==∗ resource_map_auth γ Tsh m'.
  Proof.
    iIntros "Hauth Hfrag".
    unshelve iMod (resource_map_elems_unseal with "Hfrag") as "Hfrag"; first apply readable_Tsh.
    unseal; iApply (own_update_2 with "Hauth Hfrag").
    by apply: juicy_view_free.
  Qed.

  Lemma resource_map_storebyte {γ m k v} m' v' b sh (Hsh : writable0_share sh) :
    Mem.storebytes m k.1 k.2 [b] = Some m' ->
    memval_of v' = Some b ->
    (∀ sh', sepalg.join_sub sh sh' -> Mem.perm_order'' (perm_of_res (Some (DfracOwn sh', Some v))) (perm_of_res (Some (DfracOwn sh', Some v')))) ->
    resource_map_auth γ Tsh m -∗ k ↪[γ]{DfracOwn sh} v ==∗ resource_map_auth γ Tsh m' ∗ k ↪[γ]{DfracOwn sh} v'.
  Proof.
    intros; unseal. apply bi.wand_intro_r. iIntros "[a [% f]]"; iCombine "a f" as "?".
    rewrite bi.sep_exist_l; iExists rsh.
    rewrite -!own_op.
    iApply (own_update with "[$]"). apply: juicy_view_storebyte; eauto.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma resource_map_lookup_big {γ q m} k dq m0 :
    resource_map_auth γ q m -∗
    ([∗ list] i↦v ∈ m0, adr_add k i ↪[γ]{dq} v) -∗
    ⌜forall i, i < length m0 -> coherent_loc m (adr_add k (Z.of_nat i)) (option_map (fun v => (dq, Some v)) (m0 !! i))⌝.
  Proof.
    iIntros "Hauth Hfrag". iIntros (i Hm0).
    apply lookup_lt_is_Some_2 in Hm0 as (? & Hi); rewrite Hi.
    rewrite big_sepL_lookup_acc; last done.
    iDestruct "Hfrag" as "[Hfrag ?]".
    iDestruct (resource_map_lookup with "Hauth Hfrag") as %(_ & _ & ?).
    done.
  Qed.

  Theorem resource_map_storebytes {γ m} m' k vl vl' bl sh (Hsh : writable0_share sh)
    (Hstore : Mem.storebytes m k.1 k.2 bl = Some m')
    (Hv' : Forall2 (fun v' b => memval_of v' = Some b) vl' bl)
    (Hperm : Forall2 (fun v v' => ∀ sh', sepalg.join_sub sh sh' -> Mem.perm_order'' (perm_of_res (Some (DfracOwn sh', Some v))) (perm_of_res (Some (DfracOwn sh', Some v')))) vl vl') :
    resource_map_auth γ Tsh m -∗
    ([∗ list] i↦v ∈ vl, adr_add k (Z.of_nat i) ↪[γ]{DfracOwn sh} v) ==∗
    resource_map_auth γ Tsh m' ∗
        [∗ list] i↦v ∈ vl', adr_add k (Z.of_nat i) ↪[γ]{DfracOwn sh} v.
  Proof.
    intros; iIntros "Hauth Hfrag".
    assert (readable_share sh) as rsh by auto.
    unshelve iMod (resource_map_elems_unseal with "Hfrag") as "Hfrag"; first done.
    unseal.
    rewrite (big_sepL_proper _ (λ i v, own γ (juicy_view_frag(V := leibnizO V) (adr_add k i) (DfracOwn sh) rsh v)) vl').
    2: { intros; iSplit; last eauto. iIntros "[% ?]"; by rewrite juicy_view_frag_irrel. }
    rewrite -big_opL_own_1 -own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    by apply: juicy_view_storebytes.
  Qed.

End lemmas.
