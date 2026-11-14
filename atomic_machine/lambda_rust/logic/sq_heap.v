(** Heap resources shared by the sequential and atomic-machine logics.
    Values live in the physical memory. The authority holds every allocated
    cell with fraction 1; points-to assertions own fragments of it, coupled
    with agreement on the value. *)

From iris.algebra Require Import auth gmap frac agree excl.
From iris.bi Require Import fractional.
From iris.base_logic.lib Require Export ghost_map.
From iris.proofmode Require Export proofmode.
Require Import VST.atomic_machine.atomic_machine.
Require Export VST.atomic_machine.lambda_rust.sq_sem.

Set Default Proof Using "Type".

Definition sq_heapUR : ucmra := gmapUR loc (prodR fracR (agreeR (leibnizO val))).
Definition sq_freeableUR : ucmra :=
  gmapUR block (prodR fracR (gmapR Z (exclR unitO))).

Class sq_heapGS Σ := SqHeapGS {
  sq_heap_inG :: inG Σ (authR sq_heapUR);
  sq_freeable_inG :: inG Σ (authR sq_freeableUR);
  sq_heap_name : gname;
  sq_freeable_name : gname
}.

Definition sq_heap_cells (m : lr_mem) : sq_heapUR :=
  (fun v => (1%Qp, to_agree v)) <$> m.

Lemma sq_heap_cells_lookup m l :
  sq_heap_cells m !! l = (fun v => (1%Qp, to_agree v)) <$> m !! l.
Proof. by rewrite /sq_heap_cells lookup_fmap. Qed.

Lemma sq_heap_cells_insert m l v :
  sq_heap_cells (<[l := v]> m) = <[l := (1%Qp, to_agree v)]> (sq_heap_cells m).
Proof. by rewrite /sq_heap_cells fmap_insert. Qed.

Lemma sq_heap_cells_delete m l :
  sq_heap_cells (delete l m) = delete l (sq_heap_cells m).
Proof. by rewrite /sq_heap_cells fmap_delete. Qed.

Lemma sq_heap_cells_valid m : ✓ sq_heap_cells m.
Proof. intros l. rewrite sq_heap_cells_lookup. by destruct (m !! l). Qed.

Fixpoint sq_inter (i0 : Z) (n : nat) : gmapR Z (exclR unitO) :=
  match n with O => ∅ | S n => <[i0 := Excl ()]>(sq_inter (i0+1) n) end.

Definition sq_freeable_rel (m : lr_mem) (hF : sq_freeableUR) : Prop :=
  ∀ blk qs, hF !! blk = Some qs ->
    qs.2 ≠ ∅ ∧ ∀ i, is_Some (m !! (blk, i)) ↔ is_Some (qs.2 !! i).

Section definitions.
  Context `{!sq_heapGS Σ}.

  Definition sq_pointsto (l : loc) (q : Qp) (v : val) : iProp Σ :=
    own sq_heap_name (◯ {[l := (q, to_agree v)]}).
  Definition sq_pointsto_vec (l : loc) (q : Qp) (vl : list val) : iProp Σ :=
    [∗ list] i ↦ v ∈ vl, sq_pointsto (l +ₗ i) q v.
  Definition sq_freeable (l : loc) (q : Qp) (n : nat) : iProp Σ :=
    own sq_freeable_name (◯ {[ l.1 := (q, sq_inter (l.2) n) ]}).

  Definition sq_heap (m : lr_mem) : iProp Σ :=
    ∃ hF, own sq_heap_name (● sq_heap_cells m) ∗
      own sq_freeable_name (● hF) ∗ ⌜sq_freeable_rel m hF⌝.
End definitions.

Notation "l ↦{ q } v" := (sq_pointsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (sq_pointsto l 1 v) (at level 20) : bi_scope.
Notation "l ↦∗{ q } vl" := (sq_pointsto_vec l q vl)
  (at level 20, q at level 50, format "l  ↦∗{ q }  vl") : bi_scope.
Notation "l ↦∗ vl" := (sq_pointsto_vec l 1 vl) (at level 20) : bi_scope.
Notation "†{ q } l … n" := (sq_freeable l q n)
  (at level 20, q at level 50, format "†{ q } l … n") : bi_scope.
Notation "† l … n" := (sq_freeable l 1 n) (at level 20) : bi_scope.

Local Lemma lookup_sq_alloc (σ : lr_mem) (l l' : loc) (n : nat) :
  l.1 = l'.1 → l.2 ≤ l'.2 < l.2 + n →
  alloc_gmap (LitV LitPoison) l n σ !! l' = Some (LitV LitPoison).
Proof.
  intros ?. destruct l' as [? l']; simplify_eq/=.
  revert l. induction n as [|n IH]=> /= l Hl; [lia|].
  assert (l' = l.2 ∨ l.2 + 1 ≤ l') as [->|?] by lia.
  { by rewrite -surjective_pairing lookup_insert_eq. }
  rewrite lookup_insert_ne; last by destruct l; intros ?; simplify_eq/=; lia.
  rewrite -(shift_loc_block l 1) IH /=; last lia. done.
Qed.

Local Lemma lookup_sq_alloc_ne (σ : lr_mem) (l l' : loc) (n : nat) :
  l.1 ≠ l'.1 ∨ l'.2 < l.2 ∨ l.2 + n ≤ l'.2 →
  alloc_gmap (LitV LitPoison) l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> /= l Hl; auto.
  rewrite -(IH (l +ₗ 1)); last (simpl; intuition lia).
  apply lookup_insert_ne. intros ->; intuition lia.
Qed.

Local Lemma lookup_sq_free_ne (σ : lr_mem) l l' n : l.1 ≠ l'.1 → free_gmap l n σ !! l' = σ !! l'.
Proof.
  revert l. induction n as [|n IH]=> l ? //=.
  rewrite lookup_delete_ne; last congruence.
  apply IH. by rewrite shift_loc_block.
Qed.

Local Lemma delete_sq_free {A : Type} (σ : gmap loc A) l l' n :
  delete l (free_gmap l' n σ) = free_gmap l' n (delete l σ).
Proof.
  revert l'. induction n as [|n IH]=> l' //=. by rewrite delete_delete IH.
Qed.

Section freeable.
  Implicit Types σ : lr_mem.

  Lemma sq_inter_lookup_Some i j (n : nat):
    i ≤ j < i+n → sq_inter i n !! j = Excl' ().
  Proof.
    revert i. induction n as [|n IH]=>/= i; first lia.
    rewrite lookup_insert_Some. destruct (decide (i = j)); naive_solver lia.
  Qed.
  Lemma sq_inter_lookup_None i j (n : nat):
    j < i ∨ i+n ≤ j → sq_inter i n !! j = None.
  Proof.
    revert i. induction n as [|n IH]=>/= i; first by rewrite lookup_empty.
    rewrite lookup_insert_None. naive_solver lia.
  Qed.
  Lemma sq_inter_valid i n : ✓ sq_inter i n.
  Proof. revert i. induction n as [|n IH]=>i; first done. by apply insert_valid. Qed.

  Lemma sq_freeable_rel_None σ l hF :
    (∀ m : Z, σ !! (l +ₗ m) = None) → sq_freeable_rel σ hF →
    hF !! l.1 = None.
  Proof.
    intros FRESH REL. apply eq_None_not_Some. intros [[q s] [Hsne REL']%REL].
    destruct (map_choose s) as [i []%REL'%not_eq_None_Some]; first done.
    move: (FRESH (i - l.2)). by rewrite /shift_loc Zplus_minus.
  Qed.

  Lemma sq_freeable_is_Some σ hF l n i :
    sq_freeable_rel σ hF →
    hF !! l.1 = Some (1%Qp, sq_inter (l.2) n) →
    is_Some (σ !! (l +ₗ i)) ↔ 0 ≤ i ∧ i < n.
  Proof.
    destruct l as [b j]; rewrite /shift_loc /=. intros REL Hl.
    destruct (REL b (1%Qp, sq_inter j n)) as [_ ->]; simpl in *; auto.
    destruct (decide (0 ≤ i ∧ i < n)).
    - rewrite is_Some_alt sq_inter_lookup_Some; lia.
    - rewrite is_Some_alt sq_inter_lookup_None; lia.
  Qed.

  Lemma sq_freeable_rel_alloc l h n σ:
    n ≠ O →
    (∀ m : Z, σ !! (l +ₗ m) = None) →
    sq_freeable_rel σ h →
    sq_freeable_rel (alloc_gmap (LitV LitPoison) l n σ)
                      (<[l.1 := (1%Qp, sq_inter (l.2) n)]> h).
  Proof.
    move=> Hvlnil FRESH REL blk qs /lookup_insert_Some [[<- <-]|[??]].
    - split.
      { destruct n as [|n]; simpl in *; [done|]. apply: insert_non_empty. }
      intros i. destruct (decide (l.2 ≤ i ∧ i < l.2 + n)).
      + rewrite sq_inter_lookup_Some // lookup_sq_alloc; naive_solver.
      + rewrite sq_inter_lookup_None; last lia. rewrite lookup_sq_alloc_ne /=; last lia.
        replace (l.1,i) with (l +ₗ (i - l.2)) by (rewrite /shift_loc; f_equal; lia).
        by rewrite FRESH !is_Some_alt.
    - destruct (REL blk qs) as [? Hs]; auto.
      split; [done|]=> i. by rewrite -Hs lookup_sq_alloc_ne; last auto.
  Qed.

  Lemma sq_freeable_rel_free σ hF n l :
    hF !! l.1 = Some (1%Qp, sq_inter (l.2) n) →
    sq_freeable_rel σ hF →
    sq_freeable_rel (free_gmap l n σ) (delete (l.1) hF).
  Proof.
    intros Hl REL b qs; rewrite lookup_delete_Some=> -[NEQ ?].
    destruct (REL b qs) as [? REL']; auto.
    split; [done|]=> i. by rewrite -REL' lookup_sq_free_ne.
  Qed.

  Lemma sq_freeable_rel_stable σ h l p :
    sq_freeable_rel σ h → is_Some (σ !! l) →
    sq_freeable_rel (<[l := p]>σ) h.
  Proof.
    intros REL Hσ blk qs Hqs. destruct (REL blk qs) as [? REL']; first done.
    split; [done|]=> i. rewrite -REL' lookup_insert_is_Some.
    destruct (decide (l = (blk, i))); naive_solver.
  Qed.

End freeable.

Section heap.
  Context `{!sq_heapGS Σ}.
  Implicit Types m : lr_mem.

  Global Instance sq_pointsto_timeless l q v : Timeless (l ↦{q} v).
  Proof. apply _. Qed.
  Global Instance sq_pointsto_fractional l v : Fractional (λ q, l ↦{q} v)%I.
  Proof.
    intros q1 q2. rewrite /sq_pointsto -own_op -auth_frag_op singleton_op.
    by rewrite -pair_op /= agree_idemp.
  Qed.
  Global Instance sq_pointsto_as_fractional l q v :
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split; first done. apply _. Qed.
  Global Instance sq_pointsto_vec_timeless l q vl : Timeless (l ↦∗{q} vl).
  Proof. apply _. Qed.
  Global Instance sq_freeable_timeless l q n : Timeless (†{q}l…n).
  Proof. apply _. Qed.

  Lemma sq_pointsto_vec_nil l q : l ↦∗{q} [] ⊣⊢ True.
  Proof. by rewrite /sq_pointsto_vec. Qed.
  Lemma sq_pointsto_vec_cons l q v vl :
    l ↦∗{q} (v :: vl) ⊣⊢ l ↦{q} v ∗ (l +ₗ 1) ↦∗{q} vl.
  Proof.
    rewrite /sq_pointsto_vec big_sepL_cons shift_loc_0.
    f_equiv. apply big_sepL_proper. intros k w _.
    by rewrite shift_loc_assoc Nat2Z.inj_succ Z.add_1_l.
  Qed.

  Lemma sq_pointsto_valid_2 l q1 q2 v1 v2 :
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜(q1 + q2 ≤ 1)%Qp ∧ v1 = v2⌝.
  Proof.
    iIntros "H1 H2". iCombine "H1 H2" gives %Hv.
    move: Hv. rewrite -auth_frag_op singleton_op auth_frag_valid
      singleton_valid -pair_op pair_valid /= to_agree_op_valid_L. done.
  Qed.

  Lemma sq_heap_read m l q v : sq_heap m -∗ l ↦{q} v -∗ ⌜m !! l = Some v⌝.
  Proof.
    iIntros "(%hF & Hh & _) Hl".
    iCombine "Hh Hl" gives %[Hin _]%auth_both_valid_discrete.
    iPureIntro. move: Hin=> /singleton_included_l [x [Hx Hin]].
    rewrite sq_heap_cells_lookup in Hx.
    destruct (m !! l) as [w|]; rewrite /= in Hx; last by inversion Hx.
    rewrite -Hx in Hin. move: Hin=> /Some_included [[_ Hv] | /pair_included [_ Hv]].
    - apply (inj to_agree) in Hv. by rewrite Hv.
    - apply to_agree_included in Hv. by rewrite Hv.
  Qed.

  Lemma sq_heap_write m l v v' :
    sq_heap m -∗ l ↦ v ==∗ sq_heap (<[l := v']> m) ∗ l ↦ v'.
  Proof.
    iIntros "Hm Hl". iDestruct (sq_heap_read with "Hm Hl") as %Hm.
    iDestruct "Hm" as (hF) "(Hm & HF & %HFrel)".
    iMod (own_update_2 with "Hm Hl") as "[Hm Hl]".
    { apply auth_update, (singleton_local_update _ _ (1%Qp, to_agree v)).
      - by rewrite sq_heap_cells_lookup Hm.
      - apply (exclusive_local_update _ (1%Qp, to_agree v')). done. }
    iModIntro. iFrame "Hl". iExists hF. rewrite sq_heap_cells_insert. iFrame.
    iPureIntro. eapply sq_freeable_rel_stable; first done. by exists v.
  Qed.

  Local Lemma sq_heap_alloc_values m l n :
    (∀ z : Z, m !! (l +ₗ z) = None) ->
    own sq_heap_name (● sq_heap_cells m) ==∗
    own sq_heap_name (● sq_heap_cells (alloc_gmap (LitV LitPoison) l n m)) ∗
    l ↦∗ repeat (LitV LitPoison) n.
  Proof.
    revert m l. induction n as [|n IH]=> m l Hfresh.
    { iIntros "$ !>". rewrite sq_pointsto_vec_nil. auto. }
    iIntros "Hp".
    iMod (IH m (l +ₗ 1) with "Hp") as "(Hp & Hl)".
    { intros z. by rewrite shift_loc_assoc. }
    have Hnone : alloc_gmap (LitV LitPoison) (l +ₗ 1) n m !! l = None.
    { rewrite lookup_sq_alloc_ne; last (simpl; lia).
      by rewrite -(shift_loc_0 l) Hfresh. }
    iMod (own_update with "Hp") as "[Hp Hv]".
    { apply auth_update_alloc, (alloc_singleton_local_update _ l (1%Qp, to_agree (LitV LitPoison))).
      - by rewrite sq_heap_cells_lookup Hnone.
      - done. }
    iModIntro. simpl. rewrite sq_heap_cells_insert sq_pointsto_vec_cons. iFrame.
  Qed.

  Lemma sq_heap_alloc m l (n : Z) :
    0 < n -> (∀ z, m !! (l +ₗ z) = None) ->
    sq_heap m ==∗ sq_heap (alloc_gmap (LitV LitPoison) l (Z.to_nat n) m) ∗
      †l…(Z.to_nat n) ∗ l ↦∗ repeat (LitV LitPoison) (Z.to_nat n).
  Proof.
    iIntros (Hn Hfresh) "(%hF & Hm & HF & %HFrel)".
    assert (Z.to_nat n ≠ O) by lia.
    iMod (sq_heap_alloc_values with "Hm") as "(Hm & $)"; first done.
    iMod (own_update _ (● hF) with "HF") as "[HF Hfree]".
    { apply auth_update_alloc,
        (alloc_singleton_local_update _ (l.1) (1%Qp, sq_inter (l.2) (Z.to_nat n))).
      - eauto using sq_freeable_rel_None.
      - split; first done. apply sq_inter_valid. }
    iModIntro. iFrame "Hfree". iExists _. iFrame. iPureIntro.
    by apply sq_freeable_rel_alloc.
  Qed.

  Local Lemma sq_heap_free_values m l vl :
    own sq_heap_name (● sq_heap_cells m) -∗ l ↦∗ vl ==∗
    own sq_heap_name (● sq_heap_cells (free_gmap l (length vl) m)).
  Proof.
    revert m l. induction vl as [|v vl IH]=> m l.
    { iIntros "$ _ !>". done. }
    rewrite sq_pointsto_vec_cons. iIntros "Hm [Hv Hl]".
    iMod (own_update_2 with "Hm Hv") as "Hm".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iEval (rewrite -sq_heap_cells_delete) in "Hm".
    iMod (IH (delete l m) with "Hm Hl") as "Hm".
    simpl. rewrite !delete_sq_free. by iFrame.
  Qed.

  Lemma sq_heap_free m l vl (n : Z) :
    n = length vl ->
    sq_heap m -∗ l ↦∗ vl -∗ †l…(length vl) ==∗
      ⌜0 < n⌝ ∗ ⌜∀ z, is_Some (m !! (l +ₗ z)) ↔ 0 ≤ z < n⌝ ∗
      sq_heap (free_gmap l (Z.to_nat n) m).
  Proof.
    iIntros (Hn) "(%hF & Hm & HF & %HFrel) Hl Hfree".
    iCombine "HF Hfree" gives %[Hin Hvalid]%auth_both_valid_discrete.
    move: Hin=> /singleton_included_l [[q qs] [/leibniz_equiv_iff Hlookup Hin]].
    apply (Some_included_exclusive _ _) in Hin as [=<-<-]%leibniz_equiv; last first.
    { move: (Hvalid (l.1)). rewrite Hlookup. by intros [??]. }
    assert (vl ≠ []).
    { intros ->. by destruct (HFrel (l.1) (1%Qp, ∅)) as [[] ?]. }
    assert (0 < n) by (subst n; by destruct vl).
    iMod (sq_heap_free_values with "Hm Hl") as "Hm".
    iMod (own_update_2 with "HF Hfree") as "HF".
    { apply auth_update_dealloc, (delete_singleton_local_update _ _ _). }
    iModIntro; subst n. repeat iSplit; eauto using sq_freeable_is_Some.
    iExists _. rewrite Nat2Z.id. iFrame. iPureIntro.
    by eapply sq_freeable_rel_free.
  Qed.
End heap.

(** Allocate the heap authority for an initial memory. *)
Lemma sq_heap_init `{!inG Σ (authR sq_heapUR), !inG Σ (authR sq_freeableUR)} (m : lr_mem) :
  ⊢ |==> ∃ Hheap : sq_heapGS Σ, @sq_heap Σ Hheap m.
Proof.
  iMod (own_alloc (● sq_heap_cells m)) as (vγ) "Hvγ";
    first by apply auth_auth_valid, sq_heap_cells_valid.
  iMod (own_alloc (● (∅ : sq_freeableUR))) as (fγ) "Hfγ";
    first by apply auth_auth_valid.
  iModIntro. iExists (SqHeapGS _ _ _ vγ fγ), ∅. iFrame. iPureIntro.
  intros ?? Hnone. by rewrite lookup_empty in Hnone.
Qed.
