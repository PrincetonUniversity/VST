Require Import VST.veric.base.
Require Import VST.veric.res_predicates.
Require Import VST.veric.Clight_seplog. (*need Clight_seplog rather than general seplog to ensure availability of 
                                          mapsto and memory_block -maybe move the lemmas using them elsewhere?*)
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.

Definition size_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => Ptrofs.unsigned i_ofs + sizeof t < Ptrofs.modulus
  | _ => True%type
  end.

Section mpred.

Context `{!heapGS Σ}.

Lemma nonlock_permission_bytes_valid_pointer1: forall sh b ofs n i,
  0 <= ofs /\ ofs + i < Ptrofs.modulus ->
  0 <= i < n ->
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
  + iDestruct "H" as "[% H]"; iApply (nonlock_permission_bytes_valid_pointer1 with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
Qed.

Lemma mapsto_valid_pointer: forall {cs: compspecs} sh t p v i,
  size_compatible t p -> 
  0 <= i < sizeof t ->
  mapsto sh t p v ⊢ valid_pointer (offset_val i p).
Proof.
  intros; apply mapsto_valid_pointer1; auto.
  destruct p; auto; simpl in H; lia.
Qed.

Lemma memory_block_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i < n ->
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
  + iApply (nonlock_permission_bytes_valid_pointer with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
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
  nonlock_permission_bytes sh (b, ofs) n ⊢
                           weak_valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros; iIntros "H". unfold weak_valid_pointer.
  assert (0 <= i < n \/ i = n) as [? | ?] by lia.
  - rewrite nonlock_permission_bytes_valid_pointer; [by iLeft | lia..].
  - subst i. rewrite (nonlock_permission_bytes_valid_pointer _ _ _ _ (n - 1)); [| lia..].
    iRight; rewrite /valid_pointer /valid_pointer'.
    rewrite -> !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
    replace (ofs + n + -1) with (ofs + (n - 1) + 0) by lia; done.
Qed.

Lemma memory_block_weak_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i <= n -> 0 < n ->
  memory_block sh n p ⊢ weak_valid_pointer (offset_val i p).
Proof.
  intros. unfold memory_block. destruct p; auto. iIntros "[% H]".
  pose proof Ptrofs.unsigned_range i0. rewrite -> memory_block'_eq by (rewrite ?Z2Nat.id; lia).
  unfold memory_block'_alt.
  rewrite -> Z2Nat.id by lia. destruct (readable_share_dec sh).
  + iApply (VALspec_range_weak_valid_pointer with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
  + iApply (nonlock_permission_bytes_weak_valid_pointer with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
Qed.

End mpred.
