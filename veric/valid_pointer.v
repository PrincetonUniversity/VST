Require Import VST.veric.base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.juicy_mem.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr.
Require Import VST.veric.mapsto_memory_block.

Definition size_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => Ptrofs.unsigned i_ofs + sizeof t < Ptrofs.modulus
  | _ => True%type
  end.

Section mpred.

Context `{!heapGS Σ}.

Lemma valid_pointer_dry:
  forall b ofs d m, mem_auth m ∗ valid_pointer' (Vptr b ofs) d ⊢
         ⌜Mem.valid_pointer m b (Ptrofs.unsigned ofs + d) = true⌝.
Proof.
intros.
iIntros "[Hm >H]".
iAssert ⌜∃ dq r, ✓ dq ∧ dq ≠ ε ∧ coherent_loc m (b, Ptrofs.unsigned ofs + d)%Z (dq, r)⌝ with "[-]" as %(dq & r & Hdq & ? & H).
{ iDestruct "H" as "[(% & % & H) | (% & % & H)]"; [iDestruct (mapsto_lookup with "Hm H") as %(? & ? & ? & ?) |
    iDestruct (mapsto_no_lookup with "Hm H") as %(? & ? & ?)]; iPureIntro.
  - eexists _, _; split; first done; split; last done.
    intros ->; contradiction bot_unreadable.
  - eexists (DfracOwn (Share sh)), _; split; first done; split; last done.
    intros [=]; done. }
iPureIntro.
rewrite Mem.valid_pointer_nonempty_perm /Mem.perm.
destruct H as (_ & H).
rewrite /access_cohere /access_at in H.
destruct (Maps.PMap.get _ _ _ _); try constructor.
destruct (perm_of_res_cases dq r) as [(? & -> & Hperm) | (? & Hperm)]; setoid_rewrite Hperm in H; clear Hperm.
- destruct (perm_of_dfrac dq) eqn: Hp; first done.
  apply perm_of_dfrac_None in Hp as [-> | ->]; done.
- rewrite !if_false // in H.
  intros ->; done.
Qed.

Lemma valid_pointer_dry0:
  forall m b ofs, mem_auth m ∗ valid_pointer (Vptr b ofs) ⊢
           ⌜Mem.valid_pointer m b (Ptrofs.unsigned ofs) = true⌝.
Proof.
intros.
rewrite <- (Z.add_0_r (Ptrofs.unsigned ofs)).
apply valid_pointer_dry; auto.
Qed.

Lemma weak_valid_pointer_dry:
  forall b ofs m, mem_auth m ∗ weak_valid_pointer (Vptr b ofs) ⊢
           ⌜(Mem.valid_pointer m b (Ptrofs.unsigned ofs)
            || Mem.valid_pointer m b (Ptrofs.unsigned ofs - 1))%bool = true⌝.
Proof.
intros.
rewrite orb_true_iff /weak_valid_pointer.
iIntros "[Hm [H | H]]".
- iLeft; rewrite <- (Z.add_0_r (Ptrofs.unsigned ofs)).
  iApply valid_pointer_dry; iFrame.
- iRight; rewrite <- Z.add_opp_r.
  iApply valid_pointer_dry; iFrame.
Qed.

Lemma nonlock_permission_bytes_valid_pointer1: forall sh b ofs n i,
  0 <= ofs /\ ofs + i < Ptrofs.modulus ->
  0 <= i < n ->
  sh <> Share.bot ->
  nonlock_permission_bytes sh (b, ofs) n ⊢ valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros; iIntros "H".
  rewrite /nonlock_permission_bytes /valid_pointer /=.
  rewrite -> Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  rewrite Z.add_0_r.
  rewrite (big_sepL_lookup_acc _ _ (Z.to_nat i)); last by apply lookup_seq_lt; lia.
  iDestruct "H" as "[H _]"; if_tac.
  - iDestruct "H" as "(% & % & ?)".
    rewrite /adr_add Z2Nat.id; [eauto | lia].
  - rewrite /adr_add Z2Nat.id; [auto | lia].
Qed.

Lemma nonlock_permission_bytes_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n <= Ptrofs.modulus ->
  0 <= i < n ->
  sh <> Share.bot ->
  nonlock_permission_bytes sh (b, ofs) n ⊢ valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros; apply nonlock_permission_bytes_valid_pointer1; auto; lia.
Qed.

Lemma VALspec_range_valid_pointer1: forall sh b ofs n i,
  0 <= ofs /\ ofs + i < Ptrofs.modulus ->
  0 <= i < n ->
  VALspec_range n sh (b, ofs) ⊢ valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros; iIntros "H".
  rewrite /VALspec_range /valid_pointer /=.
  rewrite -> Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
  rewrite Z.add_0_r.
  rewrite (big_sepL_lookup_acc _ _ (Z.to_nat i)); last by apply lookup_seq_lt; lia.
  iDestruct "H" as "[(% & ?) _]".
  rewrite /adr_add Z2Nat.id; [eauto | lia].
Qed.

Lemma VALspec_range_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n <= Ptrofs.modulus ->
  0 <= i < n ->
  VALspec_range n sh (b, ofs) ⊢ valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros; apply VALspec_range_valid_pointer1; auto; lia.
Qed.

Lemma address_mapsto_valid_pointer1: forall ch v sh b ofs i,
  0 <= ofs /\ ofs + i < Ptrofs.modulus ->
  0 <= i < size_chunk ch ->
  address_mapsto ch v sh (b, ofs) ⊢ valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros.
  rewrite address_mapsto_VALspec_range; apply VALspec_range_valid_pointer1; auto.
Qed.

Lemma address_mapsto_valid_pointer: forall ch v sh b ofs i,
  0 <= ofs /\ ofs + size_chunk ch <= Ptrofs.modulus ->
  0 <= i < size_chunk ch ->
  address_mapsto ch v sh (b, ofs) ⊢ valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros.
  rewrite address_mapsto_VALspec_range; apply VALspec_range_valid_pointer; auto.
Qed.

Lemma mapsto_valid_pointer1: forall {cs: compspecs} sh t p v i,
  match p with Vptr _ ofs => Ptrofs.unsigned ofs + i < Ptrofs.modulus | _ => True end ->
  0 <= i < sizeof t ->
  sh <> Share.bot ->
  mapsto sh t p v ⊢ valid_pointer (offset_val i p).
Proof.
  intros; iIntros "H".
  unfold mapsto.
  destruct (access_mode t) eqn:?H; auto.
  destruct (type_is_volatile t); auto.
  destruct p; auto.
  simpl in H; unfold sizeof in *.
  erewrite size_chunk_sizeof in H0 by eauto.
  pose proof (Ptrofs.unsigned_range i0).
  destruct (readable_share_dec sh).
  + iDestruct "H" as "[(% & H) | (% & % & H)]"; iApply (address_mapsto_valid_pointer1 with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
  + iDestruct "H" as "[% H]"; iApply (nonlock_permission_bytes_valid_pointer1 with "H"); last done; rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
Qed.

Lemma mapsto_valid_pointer: forall {cs: compspecs} sh t p v i,
  size_compatible t p -> 
  0 <= i < sizeof t ->
  sh <> Share.bot ->
  mapsto sh t p v ⊢ valid_pointer (offset_val i p).
Proof.
  intros; apply mapsto_valid_pointer1; auto.
  destruct p; auto; simpl in H; lia.
Qed.

Lemma memory_block_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i < n ->
  sh <> Share.bot ->
  memory_block sh n p ⊢ valid_pointer (offset_val i p).
Proof.
  intros.
  unfold memory_block.
  destruct p; auto.
  iIntros "[% H]".
  pose proof Ptrofs.unsigned_range i0.
  rewrite -> memory_block'_eq by (rewrite ?Z2Nat.id; lia).
  unfold memory_block'_alt.
  rewrite -> Z2Nat.id by lia.
  destruct (readable_share_dec sh).
  + iApply (VALspec_range_valid_pointer with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
  + iApply (nonlock_permission_bytes_valid_pointer with "H"); last done; rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
Qed.

Lemma VALspec_range_weak_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n < Ptrofs.modulus -> 0 <= i <= n -> 0 < n ->
  VALspec_range n sh (b, ofs) ⊢ weak_valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros; iIntros "H". unfold weak_valid_pointer.
  assert (0 <= i < n \/ i = n) as [? | ?] by lia.
  - rewrite VALspec_range_valid_pointer; [by iLeft | lia..].
  - subst i. rewrite (VALspec_range_valid_pointer _ _ _ _ (n - 1)); [| lia..].
    iRight; rewrite /valid_pointer /valid_pointer'.
    rewrite -> !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
    replace (ofs + n + -1) with (ofs + (n - 1) + 0) by lia; done.
Qed.

Lemma nonlock_permission_bytes_weak_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n < Ptrofs.modulus -> 0 <= i <= n -> 0 < n ->
  sh <> Share.bot ->
  nonlock_permission_bytes sh (b, ofs) n ⊢
                           weak_valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros; iIntros "H". unfold weak_valid_pointer.
  assert (0 <= i < n \/ i = n) as [? | ?] by lia.
  - rewrite nonlock_permission_bytes_valid_pointer //; [by iLeft | lia..].
  - subst i. rewrite (nonlock_permission_bytes_valid_pointer _ _ _ _ (n - 1)) //; [| lia..].
    iRight; rewrite /valid_pointer /valid_pointer'.
    rewrite -> !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
    replace (ofs + n + -1) with (ofs + (n - 1) + 0) by lia; done.
Qed.

Lemma memory_block_weak_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i <= n -> 0 < n ->
  sh <> Share.bot ->
  memory_block sh n p ⊢ weak_valid_pointer (offset_val i p).
Proof.
  intros. unfold memory_block. destruct p; auto. iIntros "[% H]".
  pose proof Ptrofs.unsigned_range i0. rewrite -> memory_block'_eq by (rewrite ?Z2Nat.id; lia).
  unfold memory_block'_alt.
  rewrite -> Z2Nat.id by lia. destruct (readable_share_dec sh).
  + iApply (VALspec_range_weak_valid_pointer with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
  + iApply (nonlock_permission_bytes_weak_valid_pointer with "H"); last done; rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
Qed.

End mpred.
