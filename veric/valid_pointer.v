Require Import VST.veric.base.
Require Import VST.msl.normalize.
Require Import VST.veric.compcert_rmaps.
Require Import VST.msl.msl_standard.
Require Import VST.veric.res_predicates.
Require Import VST.veric.Clight_seplog. (*need Clight_seplog rather than general seplog to ensure availability of 
                                          mapsto and memory_block -maybe move the lemmas using them elsewhere?*)
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.

Definition size_compatible {C: compspecs} t p :=
  match p with
  | Vptr b i_ofs => Ptrofs.unsigned i_ofs + sizeof t < Ptrofs.modulus
  | _ => True
  end.

Lemma nonlock_permission_bytes_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n <= Ptrofs.modulus ->
  0 <= i < n ->
  nonidentity sh ->
  nonlock_permission_bytes sh (b, ofs) n |-- valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros.
  unfold nonlock_permission_bytes, valid_pointer.
  intros w ?.
  simpl in H2 |- *.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
  rewrite Z.add_0_r.
  destruct H2 as [H2 _].
  specialize (H2 (b, ofs + i)).
  if_tac in H2.
  + destruct H2.
    destruct (w @ (b, ofs + i)); inv H2; inv H4; auto.
  + exfalso.
    simpl in H3.
    apply H3.
    split; auto.
    omega.
Qed.

Lemma VALspec_range_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n <= Ptrofs.modulus ->
  0 <= i < n ->
  VALspec_range n sh (b, ofs) |-- valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros.
  unfold VALspec_range, valid_pointer.
  intros w ?.
  simpl in H1 |- *.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
  rewrite Z.add_0_r.
  destruct H1 as [H1 _].
  specialize (H1 (b, ofs + i)).
  if_tac in H1.
  + destruct H1 as [? [? ?]].
    rewrite H1; auto.
  + exfalso.
    simpl in H2.
    apply H2.
    split; auto.
    omega.
Qed.

Lemma address_mapsto_valid_pointer: forall ch v sh b ofs i,
  0 <= ofs /\ ofs + size_chunk ch <= Ptrofs.modulus ->
  0 <= i < size_chunk ch ->
  address_mapsto ch v sh (b, ofs) |-- valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros.
  eapply derives_trans; [apply address_mapsto_VALspec_range |].
  apply VALspec_range_valid_pointer; auto.
Qed.

Lemma mapsto_valid_pointer: forall {cs: compspecs} sh t p v i,
  size_compatible t p ->
  0 <= i < sizeof t ->
  nonidentity sh ->
  mapsto sh t p v |-- valid_pointer (offset_val i p).
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t) eqn:?H; auto.
  destruct (type_is_volatile t); auto.
  destruct p; auto.
  destruct (readable_share_dec sh).
  + apply orp_left; apply andp_left2.
    - simpl in H.
      erewrite size_chunk_sizeof in H by eauto.
      erewrite size_chunk_sizeof in H0 by eauto.
      pose proof Ptrofs.unsigned_range i0.
      apply address_mapsto_valid_pointer.
      * omega.
      * rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
        omega.
    - apply exp_left; intro.
      simpl in H.
      erewrite size_chunk_sizeof in H by eauto.
      erewrite size_chunk_sizeof in H0 by eauto.
      pose proof Ptrofs.unsigned_range i0.
      apply address_mapsto_valid_pointer.
      * omega.
      * rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
        omega.
  + simpl in H.
    erewrite size_chunk_sizeof in H by eauto.
    erewrite size_chunk_sizeof in H0 by eauto.
    pose proof Ptrofs.unsigned_range i0.
    apply andp_left2.
    apply nonlock_permission_bytes_valid_pointer.
    - omega.
    - rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
      omega.
    - auto.
Qed.

Lemma memory_block_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i < n ->
  nonidentity sh ->
  memory_block sh n p |-- valid_pointer (offset_val i p).
Proof.
  intros.
  unfold memory_block.
  destruct p; auto.
  normalize.
  pose proof Ptrofs.unsigned_range i0.
  rewrite memory_block'_eq.
  2: omega.
  2: rewrite Z2Nat.id; omega.
  unfold memory_block'_alt.
  rewrite Z2Nat.id by omega.
  destruct (readable_share_dec sh).
  + apply VALspec_range_valid_pointer.
    - split; try omega.
    - rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
      auto.
  + apply nonlock_permission_bytes_valid_pointer.
    - omega.
    - rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
      omega.
    - auto.
Qed.

Lemma VALspec_range_weak_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n < Ptrofs.modulus -> 0 <= i <= n -> 0 < n ->
  VALspec_range n sh (b, ofs) |-- weak_valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros. unfold VALspec_range, weak_valid_pointer. intros w ?. simpl in H2 |- *.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
  rewrite Z.add_0_r. destruct H2 as [H2 _].
  assert (0 <= i < n \/ i = n) by omega. destruct H3.
  - specialize (H2 (b, ofs + i)). if_tac in H2.
    + left. destruct H2 as [? [? ?]]. rewrite H2; auto.
    + exfalso. simpl in H4. apply H4. split; auto. omega.
  - subst i. specialize (H2 (b, ofs + n - 1)). right. if_tac in H2.
    + destruct H2 as [? [? ?]]. replace (ofs + n + -1) with (ofs + n - 1) by omega.
      rewrite H2; auto.
    + exfalso. simpl in H3. apply H3. split; auto. omega.
Qed.

Lemma nonlock_permission_bytes_weak_valid_pointer: forall sh b ofs n i,
  0 <= ofs /\ ofs + n < Ptrofs.modulus -> 0 <= i <= n -> 0 < n -> nonidentity sh ->
  nonlock_permission_bytes sh (b, ofs) n |--
                           weak_valid_pointer (Vptr b (Ptrofs.repr (ofs + i))).
Proof.
  intros. unfold nonlock_permission_bytes, weak_valid_pointer.
  intros w ?. simpl in H3 |- *.
  rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega).
  rewrite Z.add_0_r. destruct H3 as [H3 _].
  assert (0 <= i < n \/ i = n) by omega. destruct H4.
  - left. specialize (H3 (b, ofs + i)). if_tac in H3.
    + destruct H3. destruct (w @ (b, ofs + i)); inv H3; auto.
    + exfalso. simpl in H5. apply H5. split; auto. omega.
  - subst i. right. specialize (H3 (b, ofs + n - 1)). if_tac in H3.
    + destruct H3. replace (ofs + n + -1) with (ofs + n - 1) by omega.
      destruct (w @ (b, ofs + n - 1)); inv H3; auto.
    + exfalso. simpl in H4. apply H4. split; auto. omega.
Qed.

Lemma memory_block_weak_valid_pointer: forall {cs: compspecs} sh n p i,
  0 <= i <= n -> 0 < n -> nonidentity sh ->
  memory_block sh n p |-- weak_valid_pointer (offset_val i p).
Proof.
  intros. unfold memory_block. destruct p; auto. normalize.
  pose proof Ptrofs.unsigned_range i0. rewrite memory_block'_eq.
  2: omega. 2: rewrite Z2Nat.id; omega. unfold memory_block'_alt.
  rewrite Z2Nat.id by omega. destruct (readable_share_dec sh).
  + apply VALspec_range_weak_valid_pointer; auto.
    - split; try omega.
    - rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega). auto.
  + apply nonlock_permission_bytes_weak_valid_pointer; auto.
    - omega.
    - rewrite Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; omega). omega.
Qed.
