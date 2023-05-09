(* modified from iris.base_logic.lib.ghost_map *)

(** A "ghost map" (or "ghost heap") with a proposition controlling authoritative
ownership of the entire heap, and a "points-to-like" proposition for (mutable,
fractional, or persistent read-only) ownership of individual elements. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import gmap gmap_view.
From iris_ora.logic Require Export logic own.
From VST.veric Require Import view gmap_view.
From iris.prelude Require Import options.

Class ghost_mapG Σ (K V : Type) `{Countable K} := GhostMapG {
  ghost_map_inG : inG Σ (gmap_viewR K (leibnizO V));
}.
Local Existing Instance ghost_map_inG.

Definition ghost_mapΣ (K V : Type) `{Countable K} : gFunctors :=
  #[ GFunctor (gmap_viewR K (leibnizO V)) ].

Global Instance subG_ghost_mapΣ Σ (K V : Type) `{Countable K} :
  subG (ghost_mapΣ K V) Σ → ghost_mapG Σ K V.
Proof. solve_inG. Qed.

Section definitions.
  Context `{ghost_mapG Σ K V}.

  Local Definition ghost_map_auth_def
      (γ : gname) (q : Qp) (m : gmap K V) : iProp Σ :=
    own γ (gmap_view_auth (V:=leibnizO V) (DfracOwn q) m).
  Local Definition ghost_map_auth_aux : seal (@ghost_map_auth_def).
  Proof. by eexists. Qed.
  Definition ghost_map_auth := ghost_map_auth_aux.(unseal).
  Local Definition ghost_map_auth_unseal :
    @ghost_map_auth = @ghost_map_auth_def := ghost_map_auth_aux.(seal_eq).

  Local Definition ghost_map_elem_def
      (γ : gname) (k : K) (dq : dfrac) (v : V) : iProp Σ :=
    own γ (gmap_view_frag (V:=leibnizO V) k dq v).
  Local Definition ghost_map_elem_aux : seal (@ghost_map_elem_def).
  Proof. by eexists. Qed.
  Definition ghost_map_elem := ghost_map_elem_aux.(unseal).
  Local Definition ghost_map_elem_unseal :
    @ghost_map_elem = @ghost_map_elem_def := ghost_map_elem_aux.(seal_eq).
End definitions.

Notation "k ↪[ γ ] dq v" := (ghost_map_elem γ k dq v)
  (at level 20, γ at level 50, dq custom dfrac at level 1,
   format "k  ↪[ γ ] dq  v") : bi_scope.

Local Ltac unseal := rewrite
  ?ghost_map_auth_unseal /ghost_map_auth_def
  ?ghost_map_elem_unseal /ghost_map_elem_def.

Section lemmas.
  Context `{ghost_mapG Σ K V}.
  Implicit Types (k : K) (v : V) (dq : dfrac) (q : Qp) (m : gmap K V).

  (** * Lemmas about the map elements *)
  Global Instance ghost_map_elem_timeless k γ dq v : Timeless (k ↪[γ]{dq} v).
  Proof. unseal. apply _. Qed.
  Global Instance ghost_map_elem_persistent k γ v : Persistent (k ↪[γ]□ v).
  Proof. unseal. apply own_core_persistent, view_frag_core_id, iris.algebra.gmap.gmap_singleton_core_id, _. Qed.
(*  Global Instance ghost_map_elem_fractional k γ v : Fractional (λ q, k ↪[γ]{#q} v)%I.
  Proof. unseal. intros p q. rewrite -own_op gmap_view_frag_add //. Qed.
  Global Instance ghost_map_elem_as_fractional k γ q v :
    AsFractional (k ↪[γ]{#q} v) (λ q, k ↪[γ]{#q} v)%I q.
  Proof. split; first done. apply _. Qed.*)
  Global Instance ghost_map_elem_affine k γ v : Affine (k ↪[γ]□ v).
  Proof. unseal. apply own_core_affine, view_frag_core_id, iris.algebra.gmap.gmap_singleton_core_id, _. Qed.

  Local Lemma ghost_map_elems_unseal γ m dq :
    ([∗ map] k ↦ v ∈ m, k ↪[γ]{dq} v) ==∗
    own γ ([^op map] k↦v ∈ m, gmap_view_frag (V:=leibnizO V) k dq v).
  Proof.
    unseal. destruct (decide (m = ∅)) as [->|Hne].
    - rewrite !big_opM_empty. iIntros "_". iApply own_unit.
    - rewrite big_opM_own //. iIntros "?". done.
  Qed.

  Lemma ghost_map_elem_valid k γ dq v : k ↪[γ]{dq} v -∗ ⌜✓ dq⌝.
  Proof.
    unseal. iIntros "Helem".
    iDestruct (own_valid with "Helem") as %?%gmap_view_frag_valid.
    done.
  Qed.
  Lemma ghost_map_elem_valid_2 k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %?%gmap_view_frag_op_valid_L.
    done.
  Qed.
  Lemma ghost_map_elem_agree k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "Helem1 Helem2".
    iDestruct (ghost_map_elem_valid_2 with "Helem1 Helem2") as %[_ ?].
    done.
  Qed.

  Global Instance ghost_map_elem_combine_gives γ k v1 dq1 v2 dq2 : 
    CombineSepGives (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[H1 H2].
    eauto.
  Qed.

  Lemma ghost_map_elem_combine k γ dq1 dq2 v1 v2 :
    k ↪[γ]{dq1} v1 -∗ k ↪[γ]{dq2} v2 -∗ k ↪[γ]{dq1 ⋅ dq2} v1 ∧ ⌜v1 = v2⌝.
  Proof.
    iIntros "Hl1 Hl2". iDestruct (ghost_map_elem_agree with "Hl1 Hl2") as %->.
    unseal. iCombine "Hl1 Hl2" as "Hl". rewrite -own_op gmap_view_frag_op; eauto with iFrame.
  Qed.

  Global Instance ghost_map_elem_combine_as k γ dq1 dq2 v1 v2 :
    CombineSepAs (k ↪[γ]{dq1} v1) (k ↪[γ]{dq2} v2) (k ↪[γ]{dq1 ⋅ dq2} v1) | 60. 
    (* higher cost than the Fractional instance [combine_sep_fractional_bwd],
       which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (ghost_map_elem_combine with "H1 H2") as "[$ _]".
  Qed.

  Lemma ghost_map_elem_split k γ dq1 dq2 v :
    k ↪[γ]{dq1 ⋅ dq2} v ⊣⊢ k ↪[γ]{dq1} v ∗ k ↪[γ]{dq2} v.
  Proof.
    unseal. by rewrite -own_op gmap_view_frag_op.
  Qed.

  Lemma ghost_map_elem_frac_ne γ k1 k2 dq1 dq2 v1 v2 :
    ¬ ✓ (dq1 ⋅ dq2) → k1 ↪[γ]{dq1} v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof.
    iIntros (?) "H1 H2"; iIntros (->).
    by iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[??].
  Qed.
  Lemma ghost_map_elem_ne γ k1 k2 dq2 v1 v2 :
    k1 ↪[γ] v1 -∗ k2 ↪[γ]{dq2} v2 -∗ ⌜k1 ≠ k2⌝.
  Proof. apply ghost_map_elem_frac_ne. apply: exclusive_l. Qed.

  (** Make an element read-only. *)
  Lemma ghost_map_elem_persist k γ dq v :
    k ↪[γ]{dq} v ==∗ k ↪[γ]□ v.
  Proof. intros; unseal. iApply own_update. by apply gmap_view_frag_persist. Qed.

  (** * Lemmas about [ghost_map_auth] *)
  Lemma ghost_map_alloc_strong P m :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ] v.
  Proof.
    unseal. intros.
    iMod (own_alloc_strong (gmap_view_auth (V:=leibnizO V) (DfracOwn 1) ∅) P)
      as (γ) "[% Hauth]".
    { apply gmap_view_auth_valid. }
    iExists γ. iFrame "%".
    rewrite -big_opM_own_1 -own_op. iApply (own_update with "Hauth").
    etrans; first apply: (gmap_view_alloc_big (V:=leibnizO V) _ m (DfracOwn 1)).
    - apply map_disjoint_empty_r.
    - done.
    - rewrite right_id. done.
  Qed.
  Lemma ghost_map_alloc_strong_empty P :
    pred_infinite P →
    ⊢ |==> ∃ γ, ⌜P γ⌝ ∧ ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc_strong P ∅) as (γ) "(% & Hauth & _)"; eauto.
  Qed.
  Lemma ghost_map_alloc m :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 m ∗ [∗ map] k ↦ v ∈ m, k ↪[γ] v.
  Proof.
    iMod (ghost_map_alloc_strong (λ _, True) m) as (γ) "[_ Hmap]".
    - by apply pred_infinite_True.
    - eauto.
  Qed.
  Lemma ghost_map_alloc_empty :
    ⊢ |==> ∃ γ, ghost_map_auth γ 1 (∅ : gmap K V).
  Proof.
    intros. iMod (ghost_map_alloc ∅) as (γ) "(Hauth & _)"; eauto.
  Qed.

  Global Instance ghost_map_auth_timeless γ q m : Timeless (ghost_map_auth γ q m).
  Proof. unseal. apply _. Qed.
(*  Global Instance ghost_map_auth_fractional γ m : Fractional (λ q, ghost_map_auth γ q m)%I.
  Proof. intros p q. unseal. rewrite -own_op -gmap_view_auth_dfrac_op //. Qed.
  Global Instance ghost_map_auth_as_fractional γ q m :
    AsFractional (ghost_map_auth γ q m) (λ q, ghost_map_auth γ q m)%I q.
  Proof. split; first done. apply _. Qed.*)

  Lemma ghost_map_auth_valid γ q m : ghost_map_auth γ q m -∗ ⌜✓ q⌝.
  Proof.
    unseal. iIntros "Hauth".
    iDestruct (own_valid with "Hauth") as %?%gmap_view_auth_dfrac_valid.
    done.
  Qed.
  Lemma ghost_map_auth_valid_2 γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜✓ (q1 ⋅ q2) ∧ m1 = m2⌝.
  Proof.
    unseal. iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %[??]%gmap_view_auth_dfrac_op_valid_L.
    done.
  Qed.
  Lemma ghost_map_auth_agree γ q1 q2 m1 m2 :
    ghost_map_auth γ q1 m1 -∗ ghost_map_auth γ q2 m2 -∗ ⌜m1 = m2⌝.
  Proof.
    iIntros "H1 H2".
    iDestruct (ghost_map_auth_valid_2 with "H1 H2") as %[_ ?].
    done.
  Qed.

  (** * Lemmas about the interaction of [ghost_map_auth] with the elements *)
  Lemma ghost_map_lookup {γ q m k dq v} :
    ghost_map_auth γ q m -∗ k ↪[γ]{dq} v -∗ ⌜m !! k = Some v⌝.
  Proof.
    unseal. iIntros "Hauth Hel".
    iDestruct (own_valid_2 with "Hauth Hel") as %[?[??]]%gmap_view_both_dfrac_valid_L.
    eauto.
  Qed.

  Global Instance ghost_map_lookup_combine_gives_1 {γ q m k dq v} :
    CombineSepGives (ghost_map_auth γ q m) (k ↪[γ]{dq} v) ⌜m !! k = Some v⌝.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (ghost_map_lookup with "H1 H2") as %->. eauto.
  Qed.

  Global Instance ghost_map_lookup_combine_gives_2 {γ q m k dq v} :
    CombineSepGives (k ↪[γ]{dq} v) (ghost_map_auth γ q m) ⌜m !! k = Some v⌝.
  Proof.
    rewrite /CombineSepGives comm. apply ghost_map_lookup_combine_gives_1.
  Qed.

  Lemma ghost_map_insert {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ] v.
  Proof.
    unseal. intros ?. rewrite -own_op.
    iApply own_update. apply: gmap_view_alloc; done.
  Qed.
  Lemma ghost_map_insert_persist {γ m} k v :
    m !! k = None →
    ghost_map_auth γ 1 m ==∗ ghost_map_auth γ 1 (<[k := v]> m) ∗ k ↪[γ]□ v.
  Proof.
    iIntros (?) "Hauth".
    iMod (ghost_map_insert k with "Hauth") as "[$ Helem]".
    iApply (ghost_map_elem_persist with "Helem").
  Qed.

  Lemma ghost_map_delete {γ m k v} :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (delete k m).
  Proof.
    unseal. apply bi.wand_intro_r. rewrite -own_op.
    iApply own_update. apply: gmap_view_delete.
  Qed.

  Lemma ghost_map_update {γ m k v} w :
    ghost_map_auth γ 1 m -∗ k ↪[γ] v ==∗ ghost_map_auth γ 1 (<[k := w]> m) ∗ k ↪[γ] w.
  Proof.
    unseal. apply bi.wand_intro_r. rewrite -!own_op.
    apply own_update. apply: gmap_view_update.
  Qed.

  (** Big-op versions of above lemmas *)
  Lemma ghost_map_lookup_big {γ q m} m0 :
    ghost_map_auth γ q m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) -∗
    ⌜m0 ⊆ m⌝.
  Proof.
    iIntros "Hauth Hfrag". rewrite map_subseteq_spec. iIntros (k v Hm0).
    rewrite big_sepM_lookup_acc; last done.
    iDestruct "Hfrag" as "[Hfrag ?]".
    iDestruct (ghost_map_lookup with "Hauth Hfrag") as %->.
    done.
  Qed.

  Lemma ghost_map_insert_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ 1 m ==∗
    ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ] v).
  Proof.
    unseal. intros ?. rewrite -big_opM_own_1 -own_op.
    apply own_update. apply: gmap_view_alloc_big; done.
  Qed.
  Lemma ghost_map_insert_persist_big {γ m} m' :
    m' ##ₘ m →
    ghost_map_auth γ 1 m ==∗
    ghost_map_auth γ 1 (m' ∪ m) ∗ ([∗ map] k ↦ v ∈ m', k ↪[γ]□ v).
  Proof.
    iIntros (Hdisj) "Hauth".
    iMod (ghost_map_insert_big m' with "Hauth") as "[$ Helem]".
    iApply big_sepM_bupd. iApply (big_sepM_impl with "Helem").
    iIntros "!#" (k v) "_". iApply ghost_map_elem_persist.
  Qed.

  Lemma ghost_map_delete_big {γ m} m0 :
    ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ 1 (m ∖ m0).
  Proof.
    iIntros "Hauth Hfrag". iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. iApply (own_update_2 with "Hauth Hfrag").
    apply: gmap_view_delete_big.
  Qed.

  Theorem ghost_map_update_big {γ m} m0 m1 :
    dom m0 = dom m1 →
    ghost_map_auth γ 1 m -∗
    ([∗ map] k↦v ∈ m0, k ↪[γ] v) ==∗
    ghost_map_auth γ 1 (m1 ∪ m) ∗
        [∗ map] k↦v ∈ m1, k ↪[γ] v.
  Proof.
    iIntros (?) "Hauth Hfrag". iMod (ghost_map_elems_unseal with "Hfrag") as "Hfrag".
    unseal. rewrite -big_opM_own_1 -own_op.
    iApply (own_update_2 with "Hauth Hfrag").
    apply: gmap_view_update_big. done.
  Qed.

End lemmas.
