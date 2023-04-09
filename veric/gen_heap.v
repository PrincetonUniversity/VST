(* modified from iris.base_logic.lib.gen_heap *)

From stdpp Require Export namespaces.
From iris.algebra Require Import reservation_map.
From iris.algebra Require Import agree.
From iris_ora.algebra Require Import agree.
From VST.veric Require Export dfrac juicy_view.
From iris.proofmode Require Import proofmode.
From iris_ora.logic Require Export logic own.
From VST.veric Require Import ghost_map resource_map ext_order.
From iris.prelude Require Import options.

(** This file defines the language-level points-to
connective [l ↦{dq} v] reflecting the physical heap.  This library is designed to
be used as a singleton (i.e., with only a single instance existing in any
proof), with the [gen_heapGS] typeclass providing the ghost names of that unique
instance.  That way, [mapsto] does not need an explicit [gname] parameter.
This mechanism can be plugged into a language and related to the physical heap
by using [gen_heap_interp σ] in the state interpretation of the weakest
precondition. See heap-lang for an example.

This library is generic in the type [V] for values and
supports fractional permissions.  Next to the point-to connective [l ↦{dq} v],
which keeps track of the value [v] of a location [l], this library also provides
a way to attach "meta" or "ghost" data to locations. This is done as follows:

- When one allocates a location, in addition to the point-to connective [l ↦ v],
  one also obtains the token [meta_token l ⊤]. This token is an exclusive
  resource that denotes that no meta data has been associated with the
  namespaces in the mask [⊤] for the location [l].
- Meta data tokens can be split w.r.t. namespace masks, i.e.
  [meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2] if [E1 ## E2].
- Meta data can be set using the update [meta_token l E ==∗ meta l N x] provided
  [↑N ⊆ E], and [x : A] for any countable [A]. The [meta l N x] connective is
  persistent and denotes the knowledge that the meta data [x] has been
  associated with namespace [N] to the location [l].

To make the mechanism as flexible as possible, the [x : A] in [meta l N x] can
be of any countable type [A]. This means that you can associate e.g. single
ghost names, but also tuples of ghost names, etc.

To further increase flexibility, the [meta l N x] and [meta_token l E]
connectives are annotated with a namespace [N] and mask [E]. That way, one can
assign a map of meta information to a location. This is particularly useful when
building abstractions, then one can gradually assign more ghost information to a
location instead of having to do all of this at once. We use namespaces so that
these can be matched up with the invariant namespaces. *)

(** To implement this mechanism, we use three resource algebras:

- A [gmap_view address V], which keeps track of the values of locations.
- A [gmap_view address gname], which keeps track of the meta information of
  locations. More specifically, this RA introduces an indirection: it keeps
  track of a ghost name for each location.
- The ghost names in the aforementioned authoritative RA refer to namespace maps
  [reservation_map (agree positive)], which store the actual meta information.
  This indirection is needed because we cannot perform frame preserving updates
  in an authoritative fragment without owning the full authoritative element
  (in other words, without the indirection [meta_set] would need [gen_heap_interp]
  as a premise).
 *)

(** The ORAs we need, and the global ghost names we are using. *)

(* is this right? *)
Canonical Structure reservation_mapR := inclR (reservation_mapR (agreeR positiveO)).

Global Instance reservation_map_data_core_id k (a : agreeR positiveO) :
    OraCoreId a → OraCoreId(A := reservation_mapR) (reservation_map_data(A := agreeR positiveO) k a).
Proof. do 2 constructor; simpl; auto. apply core_id_core, _. Qed.

Global Instance reservation_map_ora_discrete : OraDiscrete reservation_mapR.
Proof.
  split; first apply _.
  - intros [m [E|]]; rewrite reservation_map_validN_eq reservation_map_valid_eq //=.
    by intros [?%cmra_discrete_valid ?].
  - intros ?? [? [H1 H2]] ?.
    apply gmap_cmra_discrete in H1; last apply _.
    eexists; split; eauto.
    by apply equiv_dist.
Qed.

Class gen_heapGpreS (V : Type) (Σ : gFunctors) `{resource_ops (leibnizO V)} := {
  gen_heapGpreS_heap : resource_mapG Σ V;
  gen_heapGpreS_meta : ghost_mapG Σ address gname;
  gen_heapGpreS_meta_data : inG Σ reservation_mapR;
}.
Local Existing Instances gen_heapGpreS_meta_data gen_heapGpreS_heap gen_heapGpreS_meta.

Class gen_heapGS (V : Type) (Σ : gFunctors) `{resource_ops (leibnizO V)} := GenHeapGS {
  gen_heap_inG : gen_heapGpreS V Σ;
  gen_heap_name : gname;
  gen_meta_name : gname
}.
Local Existing Instance gen_heap_inG.
Global Arguments GenHeapGS V Σ {_ _} _ _.
Global Arguments gen_heap_name {V Σ _} _ : assert.
Global Arguments gen_meta_name {V Σ _} _ : assert.

Definition gen_heapΣ (V : Type) `{resource_ops (leibnizO V)} : gFunctors := #[
  resource_mapΣ V;
  ghost_mapΣ address gname;
  GFunctor reservation_mapR
].

Global Instance subG_gen_heapGpreS {Σ V} `{resource_ops (leibnizO V)} :
  subG (gen_heapΣ V) Σ → gen_heapGpreS V Σ.
Proof. solve_inG. Qed.

Section definitions.
  Context `{ResOps : resource_ops (leibnizO V)} `{hG : !gen_heapGS V Σ}.

  Definition gen_heap_interp (σ : mem) : iProp Σ := ∃ m : gmap address gname,
(*    (* The [⊆] is used to avoid assigning ghost information to the locations in
    the initial heap (see [gen_heap_init]). *)
    ⌜ dom m ⊆ dom σ ⌝ ∧ *)
    resource_map_auth (gen_heap_name hG) Tsh σ ∗
    ghost_map_auth (gen_meta_name hG) Tsh m.

  Local Definition mapsto_def (l : address) (dq : dfrac) (v: V) : iProp Σ :=
    l ↪[gen_heap_name hG]{dq} v.
  Local Definition mapsto_aux : seal (@mapsto_def). Proof. by eexists. Qed.
  Definition mapsto := mapsto_aux.(unseal).
  Local Definition mapsto_unseal : @mapsto = @mapsto_def := mapsto_aux.(seal_eq).

  Local Definition mapsto_no_def (l : address) (sh : share) (rsh : ~readable_share sh) : iProp Σ :=
    resource_map_elem_no (gen_heap_name hG) l sh rsh.
  Local Definition mapsto_no_aux : seal (@mapsto_no_def). Proof. by eexists. Qed.
  Definition mapsto_no := mapsto_no_aux.(unseal).
  Local Definition mapsto_no_unseal : @mapsto_no = @mapsto_no_def := mapsto_no_aux.(seal_eq).

  Local Definition meta_token_def (l : address) (E : coPset) : iProp Σ :=
    ∃ γm, ghost_map_elem (gen_meta_name hG) l DfracDiscarded γm ∗ own(A := reservation_mapR) γm (reservation_map_token E).
  Local Definition meta_token_aux : seal (@meta_token_def). Proof. by eexists. Qed.
  Definition meta_token := meta_token_aux.(unseal).
  Local Definition meta_token_unseal :
    @meta_token = @meta_token_def := meta_token_aux.(seal_eq).

  (** TODO: The use of [positives_flatten] violates the namespace abstraction
  (see the proof of [meta_set]. *)
  Local Definition meta_def `{Countable A} (l : address) (N : namespace) (x : A) : iProp Σ :=
    ∃ γm, ghost_map_elem (gen_meta_name hG) l DfracDiscarded γm ∗
          own(A := reservation_mapR) γm (reservation_map_data (positives_flatten N) (to_agree (encode x))).
  Local Definition meta_aux : seal (@meta_def). Proof. by eexists. Qed.
  Definition meta := meta_aux.(unseal).
  Local Definition meta_unseal : @meta = @meta_def := meta_aux.(seal_eq).
End definitions.
Global Arguments meta {V _ Σ _ A _ _} l N x.

Local Notation "l ↦ dq v" := (mapsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.

Section gen_heap.
  Context {V} `{resource_ops (leibnizO V), !gen_heapGS V Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types Φ : V → iProp Σ.
  Implicit Types σ : gmap address V.
  Implicit Types m : mem.
  Implicit Types l : address.
  Implicit Types v : V.

  (** General properties of mapsto *)
  Global Instance mapsto_timeless l dq (rsh : readable_dfrac dq) v : Timeless (l ↦{dq} v).
  Proof. rewrite mapsto_unseal. apply _. Qed.
(*  Global Instance mapsto_fractional l v : Fractional (λ q, l ↦{#q} v)%I.
  Proof. rewrite mapsto_unseal. apply _. Qed.
  Global Instance mapsto_as_fractional l q v :
    AsFractional (l ↦{#q} v) (λ q, l ↦{#q} v)%I q.
  Proof. rewrite mapsto_unseal. apply _. Qed. *)
(*  Global Instance mapsto_persistent l v : Persistent (l ↦□ v).
  Proof. rewrite mapsto_unseal. apply _. Qed.
  Global Instance mapsto_affine l v : Affine (l ↦□ v).
  Proof. rewrite mapsto_unseal. apply _. Qed.*)

  Lemma mapsto_valid l dq v : l ↦{dq} v -∗ ⌜✓ dq ∧ readable_dfrac dq⌝%Qp.
  Proof. rewrite mapsto_unseal. apply resource_map_elem_valid. Qed.
  Lemma mapsto_valid_2 l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ readable_dfrac (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof. rewrite mapsto_unseal. apply resource_map_elem_valid_2. Qed.
  (** Almost all the time, this is all you really need. *)
  Lemma mapsto_agree l dq1 dq2 v1 v2 : l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ ⌜v1 = v2⌝.
  Proof. rewrite mapsto_unseal. apply resource_map_elem_agree. Qed.

  Lemma mapsto_no_valid_2 l dq1 dq2 nsh1 nsh2 : mapsto_no l dq1 nsh1 -∗ mapsto_no l dq2 nsh2 -∗ ⌜✓ (dq1 ⋅ dq2)⌝.
  Proof. rewrite mapsto_no_unseal. apply resource_map_elem_no_valid_2. Qed.

  Global Instance mapsto_combine_sep_gives l dq1 dq2 v1 v2 : 
    CombineSepGives (l ↦{dq1} v1) (l ↦{dq2} v2) ⌜✓ (dq1 ⋅ dq2) ∧ readable_dfrac (dq1 ⋅ dq2) ∧ v1 = v2⌝ | 30.
  Proof.
    rewrite /CombineSepGives. iIntros "[H1 H2]".
    iDestruct (mapsto_valid_2 with "H1 H2") as %?. eauto.
  Qed.

  Lemma mapsto_combine l dq1 dq2 v1 v2 :
    l ↦{dq1} v1 -∗ l ↦{dq2} v2 -∗ l ↦{dq1 ⋅ dq2} v1 ∧ ⌜v1 = v2⌝.
  Proof. rewrite mapsto_unseal. apply resource_map_elem_combine. Qed.

  Global Instance mapsto_combine_as l dq1 dq2 v1 v2 :
    CombineSepAs (l ↦{dq1} v1) (l ↦{dq2} v2) (l ↦{dq1 ⋅ dq2} v1) | 60.
    (* higher cost than the Fractional instance, which kicks in for #qs *)
  Proof.
    rewrite /CombineSepAs. iIntros "[H1 H2]".
    iDestruct (mapsto_combine with "H1 H2") as "(? & _)"; eauto.
  Qed.

  Lemma mapsto_split l dq1 dq2 (rsh1 : readable_dfrac dq1) (rsh2 : readable_dfrac dq2) v :
    l ↦{dq1 ⋅ dq2} v ⊣⊢ l ↦{dq1} v ∗ l ↦{dq2} v.
  Proof. rewrite mapsto_unseal. by apply resource_map_elem_split. Qed.

  Lemma mapsto_frac_ne l1 l2 dq1 dq2 v1 v2 :
    ¬ ✓(dq1 ⋅ dq2) → l1 ↦{dq1} v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite mapsto_unseal. apply resource_map_elem_frac_ne. Qed.
  Lemma mapsto_ne l1 l2 dq2 v1 v2 : l1 ↦ v1 -∗ l2 ↦{dq2} v2 -∗ ⌜l1 ≠ l2⌝.
  Proof. rewrite mapsto_unseal. apply resource_map_elem_ne. Qed.

  (** Permanently turn any points-to predicate into a persistent
      points-to predicate. *)
  Lemma mapsto_persist l dq v : l ↦{dq} v ==∗ l ↦□ v.
  Proof. rewrite mapsto_unseal. apply resource_map_elem_persist. Qed.

  (** Framing support *)
(*  Global Instance frame_mapsto p l v q1 q2 RES :
    FrameFractionalHyps p (l ↦{#q1} v) (λ q, l ↦{#q} v)%I RES q1 q2 →
    Frame p (l ↦{#q1} v) (l ↦{#q2} v) RES | 5.
  Proof. apply: frame_fractional. Qed. *)

  (** General properties of [meta] and [meta_token] *)
  Global Instance meta_token_timeless l N : Timeless (meta_token l N).
  Proof. rewrite meta_token_unseal. apply _. Qed.
  Global Instance meta_timeless `{Countable A} l N (x : A) : Timeless (meta l N x).
  Proof. rewrite meta_unseal. apply _. Qed.
  Global Instance meta_persistent `{Countable A} l N (x : A) : Persistent (meta l N x).
  Proof. rewrite meta_unseal. apply _. Qed.

  Lemma meta_token_union_1 l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) -∗ meta_token l E1 ∗ meta_token l E2.
  Proof.
    rewrite meta_token_unseal /meta_token_def. intros ?. iDestruct 1 as (γm1) "[#Hγm Hm]".
    rewrite reservation_map_token_union //. iDestruct "Hm" as "[Hm1 Hm2]".
    iSplitL "Hm1"; eauto.
  Qed.
  Lemma meta_token_union_2 l E1 E2 :
    meta_token l E1 -∗ meta_token l E2 -∗ meta_token l (E1 ∪ E2).
  Proof.
    rewrite meta_token_unseal /meta_token_def.
    iIntros "(%γm1 & #Hγm1 & Hm1) (%γm2 & #Hγm2 & Hm2)".
    iDestruct (ghost_map_elem_valid_2 with "Hγm1 Hγm2") as %[_ ->].
    iDestruct (own_valid_2 with "Hm1 Hm2") as %?%reservation_map_token_valid_op.
    iExists γm2. iFrame "Hγm2". rewrite reservation_map_token_union //. by iSplitL "Hm1".
  Qed.
  Lemma meta_token_union l E1 E2 :
    E1 ## E2 → meta_token l (E1 ∪ E2) ⊣⊢ meta_token l E1 ∗ meta_token l E2.
  Proof.
    intros; iSplit; first by iApply meta_token_union_1.
    iIntros "[Hm1 Hm2]". by iApply (meta_token_union_2 with "Hm1 Hm2").
  Qed.

  Lemma meta_token_difference l E1 E2 :
    E1 ⊆ E2 → meta_token l E2 ⊣⊢ meta_token l E1 ∗ meta_token l (E2 ∖ E1).
  Proof.
    intros. rewrite {1}(union_difference_L E1 E2) //.
    by rewrite meta_token_union; last set_solver.
  Qed.

  Lemma meta_agree `{Countable A} l i (x1 x2 : A) :
    meta l i x1 -∗ meta l i x2 -∗ ⌜x1 = x2⌝.
  Proof.
    rewrite meta_unseal /meta_def.
    iIntros "(%γm1 & Hγm1 & Hm1) (%γm2 & Hγm2 & Hm2)".
    iDestruct (ghost_map_elem_valid_2 with "Hγm1 Hγm2") as %[_ ->].
    iDestruct (own_valid_2 with "Hm1 Hm2") as %Hγ; iPureIntro.
    move: Hγ. rewrite -reservation_map_data_op reservation_map_data_valid.
    move=> /to_agree_op_inv_L. naive_solver.
  Qed.
  Lemma meta_set `{Countable A} E l (x : A) N :
    ↑ N ⊆ E → meta_token l E ==∗ meta l N x.
  Proof.
    rewrite meta_token_unseal meta_unseal /meta_token_def /meta_def.
    iDestruct 1 as (γm) "[Hγm Hm]". iExists γm. iFrame "Hγm".
    iApply (own_update with "Hm").
    apply reservation_map_alloc; last done.
    cut (positives_flatten N ∈@{coPset} ↑N); first by set_solver.
    (* TODO: Avoid unsealing here. *)
    rewrite namespaces.nclose_unseal. apply elem_coPset_suffixes.
    exists 1%positive. by rewrite left_id_L.
  Qed.

(*  (** Update lemmas *)
  Lemma gen_heap_alloc σ l v :
    σ !! l = None →
    gen_heap_interp σ ==∗ gen_heap_interp (<[l:=v]>σ) ∗ l ↦ v ∗ meta_token l ⊤.
  Proof.
    iIntros (Hσl). rewrite /gen_heap_interp mapsto_unseal /mapsto_def meta_token_unseal /meta_token_def /=.
    iDestruct 1 as (m Hσm) "[Hσ Hm]".
    iMod (ghost_map_insert l with "Hσ") as "[Hσ Hl]".
    iMod (own_alloc(A := reservation_mapR) (reservation_map_token ⊤)) as (γm) "Hγm".
    { apply reservation_map_token_valid. }
    iMod (ghost_map_insert_persist l with "Hm") as "[Hm Hlm]".
    { move: Hσl. rewrite -!not_elem_of_dom. set_solver. }
    iModIntro. iFrame "Hl". iSplitL "Hσ Hm"; last by eauto with iFrame.
    iExists (<[l:=γm]> m). iFrame. iPureIntro.
    rewrite !dom_insert_L. set_solver.
  Qed.

  Lemma gen_heap_alloc_big σ σ' :
    σ' ##ₘ σ →
    gen_heap_interp σ ==∗
    gen_heap_interp (σ' ∪ σ) ∗ ([∗ map] l ↦ v ∈ σ', l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ', meta_token l ⊤).
  Proof.
    revert σ; induction σ' as [| l v σ' Hl IH] using map_ind; iIntros (σ Hdisj) "Hσ".
    { rewrite left_id_L !big_sepM_empty. auto. }
    iMod (IH with "Hσ") as "[Hσ'σ Hσ']"; first by eapply map_disjoint_insert_l.
    decompose_map_disjoint.
    rewrite !big_opM_insert // -insert_union_l //.
    by iMod (gen_heap_alloc with "Hσ'σ") as "($ & $ & $)";
      first by apply lookup_union_None.
  Qed.*)

  Lemma mapsto_lookup m l dq v : resource_map_auth (gen_heap_name _) Tsh m -∗ l ↦{dq} v -∗ ⌜✓ dq ∧ readable_dfrac dq ∧ coherent_loc m l (Some (dq, Some v))⌝.
  Proof. rewrite mapsto_unseal. apply resource_map_lookup. Qed.

  Lemma mapsto_lookup_big m l dq (m0 : list V) :
    resource_map_auth (gen_heap_name _) Tsh m -∗
    ([∗ list] i↦v ∈ m0, adr_add l i ↦{dq} v) -∗
    ⌜forall i, i < length m0 -> coherent_loc m (adr_add l (Z.of_nat i)) (option_map (fun v => (dq, Some v)) (m0 !! i))⌝.
  Proof. rewrite mapsto_unseal. apply resource_map_lookup_big. Qed.

  Lemma mapsto_storebyte m k b m' v v' sh (Hsh : writable0_share sh) :
    Mem.storebytes m k.1 k.2 [b] = Some m' ->
    memval_of v' = Some b ->
    (∀ sh', sepalg.join_sub sh sh' -> Mem.perm_order'' (perm_of_res (Some (DfracOwn sh', Some v))) (perm_of_res (Some (DfracOwn sh', Some v')))) ->
    resource_map_auth (gen_heap_name _) Tsh m -∗ k ↦{DfracOwn sh} v ==∗ resource_map_auth (gen_heap_name _) Tsh m' ∗ k ↦{DfracOwn sh} v'.
  Proof. rewrite mapsto_unseal. by apply resource_map_storebyte. Qed.

  Lemma mapsto_storebytes m m' k vl vl' bl sh (Hsh : writable0_share sh)
    (Hstore : Mem.storebytes m k.1 k.2 bl = Some m')
    (Hv' : Forall2 (fun v' b => memval_of v' = Some b) vl' bl)
    (Hperm : Forall2 (fun v v' => forall sh', sepalg.join_sub sh sh' -> Mem.perm_order'' (perm_of_res (Some (DfracOwn sh', Some v))) (perm_of_res (Some (DfracOwn sh', Some v')))) vl vl') :
    resource_map_auth (gen_heap_name _) Tsh m -∗
    ([∗ list] i↦v ∈ vl, adr_add k (Z.of_nat i) ↦{DfracOwn sh} v) ==∗
    resource_map_auth (gen_heap_name _) Tsh m' ∗
        [∗ list] i↦v ∈ vl', adr_add k (Z.of_nat i) ↦{DfracOwn sh} v.
  Proof. rewrite mapsto_unseal. eapply resource_map_storebytes; eauto. Qed.

End gen_heap.

(*
(** This variant of [gen_heap_init] should only be used when absolutely needed.
The key difference to [gen_heap_init] is that the [inG] instances in the new
[gen_heapGS] instance are related to the original [gen_heapGpreS] instance,
whereas [gen_heap_init] forgets about that relation. *)
Lemma gen_heap_init_names `{!gen_heapGpreS V Σ} σ :
  ⊢ |==> ∃ γh γm : gname,
    let hG := GenHeapGS address V Σ γh γm in
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (ghost_map_alloc_empty (K:=L) (V:=V)) as (γh) "Hh".
  iMod (ghost_map_alloc_empty (K:=L) (V:=gname)) as (γm) "Hm".
  iExists γh, γm.
  iAssert (gen_heap_interp (hG:=GenHeapGS _ _ _ γh γm) ∅) with "[Hh Hm]" as "Hinterp".
  { iExists ∅; simpl. iFrame "Hh Hm". by rewrite dom_empty_L. }
  iMod (gen_heap_alloc_big with "Hinterp") as "(Hinterp & $ & $)".
  { apply map_disjoint_empty_r. }
  rewrite right_id_L. done.
Qed.

Lemma gen_heap_init `{!gen_heapGpreS V Σ} σ :
  ⊢ |==> ∃ _ : gen_heapGS V Σ,
    gen_heap_interp σ ∗ ([∗ map] l ↦ v ∈ σ, l ↦ v) ∗ ([∗ map] l ↦ _ ∈ σ, meta_token l ⊤).
Proof.
  iMod (gen_heap_init_names σ) as (γh γm) "Hinit".
  iExists (GenHeapGS _ _ _ γh γm).
  done.
Qed.
*)
