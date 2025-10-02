Require Import VST.veric.base.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.res_predicates.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.juicy_mem.
Require Import VST.veric.assert_lemmas.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.address_conflict.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.Cop2.
Require Import VST.veric.shares.
Require Import VST.veric.slice.
Require Import VST.veric.mpred.
Require Import VST.veric.log_normalize.
Require Import VST.veric.expr.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.mapsto_memory_block.
Require Import VST.veric.valid_pointer.

Section mpred.

Context `{!heapGS Σ}.

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch =>
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs =>
       if readable_share_dec sh
       then ⌜tc_val' t v2⌝ ∧ address_mapsto ch v2 sh (b, Ptrofs.unsigned ofs)
       else ⌜tc_val' t v2 /\ (align_chunk ch | Ptrofs.unsigned ofs)⌝ ∧ nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs) (size_chunk ch)
     | _ => False
    end
    | _ => False
    end
  | _ => False
  end.

Definition mapsto_ sh t v1 := ∃ v, mapsto sh t v1 v.

Lemma mapsto_tc_val': forall sh t p v, mapsto sh t p v ⊢ ⌜tc_val' t v⌝.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  if_tac; auto;
  destruct p; auto;
  try simple_if_tac; auto.
  + iIntros "[$ _]".
  + iIntros "[[$ _] _]".
Qed.

Lemma mapsto_weaken: forall sh t p v, mapsto sh t p v ⊢ mapsto_memory_block.mapsto sh t p v.
Proof.
  intros; rewrite /mapsto /mapsto_memory_block.mapsto.
  destruct (access_mode t); try done.
  destruct (type_is_volatile t); try done.
  destruct p; try done.
  if_tac; try done.
  iIntros "(% & H)".
  destruct (eq_dec v Vundef).
  - subst; iRight; eauto.
  - iLeft; iFrame; auto.
Qed.

Lemma mapsto_eq: forall sh t p v, v ≠ Vundef -> mapsto_memory_block.mapsto sh t p v = mapsto sh t p v.
Proof.
  intros; rewrite /mapsto /mapsto_memory_block.mapsto.
  destruct (access_mode t); try done.
  destruct (type_is_volatile t); try done.
  destruct p; try done.
  if_tac; try done.
  rewrite (prop_false_andp _ _ H) False_or.
  do 2 f_equal; apply prop_ext.
  rewrite /tc_val'; tauto.
Qed.

Fixpoint memory_block' (sh: share) (n: nat) (b: block) (i: Z) : mpred :=
  match n with
  | O => emp
  | S n' => (if readable_share_dec sh then (b, i) ↦{#sh} VAL Undef
             else nonlock_permission_bytes sh (b, i) 1)
         ∗ memory_block' sh n' b (i+1)
  end.

Definition memory_block'_alt (sh: share) (n: nat) (b: block) (ofs: Z) : mpred :=
 if readable_share_dec sh
 then [∗ list] i ∈ seq 0 n, (adr_add (b, ofs) (Z.of_nat i)) ↦{#sh} VAL Undef
 else nonlock_permission_bytes sh (b,ofs) (Z.of_nat n).

Lemma memory_block'_eq:
 forall sh n b i,
  0 <= i ->
  Z_of_nat n + i < Ptrofs.modulus ->
  memory_block' sh n b i ⊣⊢ memory_block'_alt sh n b i.
Proof.
  intros.
  unfold memory_block'_alt.
  revert i H H0; induction n; intros.
  + if_tac; reflexivity.
  + unfold memory_block'; fold memory_block'.
    rewrite -> (IHn (i+1)) by (rewrite inj_S in H0; lia).
    if_tac.
    - simpl; f_equiv.
      * rewrite /adr_add /= Z.add_0_r //.
      * rewrite -(fmap_add_seq 1 0) big_sepL_fmap; do 3 f_equiv.
        rewrite /adr_add /=; do 2 f_equiv; lia.
    - rewrite -> (nonlock_permission_bytes_split2 1 (Z_of_nat n) (Z.of_nat (S n))) by (try rewrite inj_S; lia); done.
Qed.

Definition memory_block (sh: share) (n: Z) (v: val) : mpred :=
 match v with
 | Vptr b ofs => ⌜Ptrofs.unsigned ofs + n < Ptrofs.modulus⌝ ∧ memory_block' sh (Z.to_nat n) b (Ptrofs.unsigned ofs)
 | _ => False
 end.

Lemma memory_block_weaken: forall sh n v, memory_block sh n v ⊢ mapsto_memory_block.memory_block sh n v.
Proof.
  intros; rewrite /memory_block /mapsto_memory_block.memory_block.
  destruct v; try done.
  iIntros "(% & H)"; iSplit; first done; iStopProof.
  destruct (zlt n 0).
  { rewrite Z2Nat_neg //. }
  rewrite -(Z2Nat.id n) in H; last lia.
  generalize dependent i; induction (Z.to_nat n); simpl; intros; first done.
  f_equiv.
  - rewrite Ptrofs.repr_unsigned /mapsto_memory_block.mapsto_ /mapsto_memory_block.mapsto /=.
    if_tac.
    + iIntros "H"; iRight; iSplit; first done.
      rewrite address_mapsto_undef; iFrame.
    + iIntros "$"; iPureIntro; split; last done.
      split; [apply tc_val'_Vundef | apply Z.divide_1_l].
  - specialize (IHn0 (Ptrofs.add i Ptrofs.one)).
    rewrite Ptrofs.add_unsigned Ptrofs.unsigned_repr Ptrofs.unsigned_one in IHn0.
    apply IHn0; lia.
    { unfold Ptrofs.max_unsigned; pose proof (Ptrofs.unsigned_range i); lia. }
Qed.

Lemma mapsto__exp_address_mapsto: forall sh t b i_ofs ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  readable_share sh ->
  mapsto_ sh t (Vptr b i_ofs) ⊣⊢ ∃ v2' : val, <affine> ⌜tc_val' t v2'⌝ ∗
            address_mapsto ch v2' sh (b, (Ptrofs.unsigned i_ofs)).
Proof.
  intros.
  unfold mapsto_, mapsto; do 2 f_equiv.
  rewrite H H0.
  rewrite -> if_true by auto.
  apply bi.persistent_and_affinely_sep_l; apply _.
Qed.

(*Lemma mapsto__memory_block: forall sh b ofs t ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  mapsto sh t (Vptr b ofs) Vundef ⊣⊢ memory_block sh (size_chunk ch) (Vptr b ofs).
Proof.
  intros.
  unfold mapsto_, mapsto, memory_block, memory_block'.
  pose proof (tc_val'_Vundef t).
  rewrite H H0 (pure_True _ H2) !pure_True // !True_and.
  if_tac.
  - iIntros "(% & % & % & % & H)".
    rewrite address_mapsto_VALspec_range /VALspec_range.
    forget (Ptrofs.unsigned ofs) as o.
    clear - H3; iInduction (Z.to_nat (size_chunk ch)) as [|] "IH" forall (o); simpl; first done.
    rewrite /mapsto_ /mapsto /=.
    iDestruct "H" as "(H & Hrest)"; iSplitL "H".
    + Search VALspec_range address_mapsto.
    Search seq S.
big_sepL_snoc
    Search big_opL bi_sep app.
  if_tac.
  trans (∃ v : val,
   if readable_share_dec sh
   then ⌜tc_val' t v⌝ ∧ address_mapsto ch v sh (b, Ptrofs.unsigned ofs)
   else
    ⌜tc_val' t v⌝
    ∧ nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs) (size_chunk ch)).
  { do 2 f_equiv.
    rewrite pure_and (pure_True _ H1) and_True //. }
  rewrite (pure_True _ H2) True_and.
  clear.
  remember (Z.to_nat (size_chunk ch)) as n; generalize dependent ch; induction n; simpl; intros.
  - 
  setoid_rewrite bi.pure_and.
  rewrite memory_block'_eq.
  2: pose proof Ptrofs.unsigned_range ofs; lia.
  2: rewrite -> Z2Nat.id by (pose proof size_chunk_pos ch; lia); lia.
  rewrite bi.pure_True; last done.
  rewrite bi.True_and.
  unfold memory_block'_alt; destruct (readable_share_dec sh).
 * rewrite -> mapsto__exp_address_mapsto with (ch := ch); auto.
  rewrite -> Z2Nat.id by (pose proof size_chunk_pos ch; lia).
  rewrite -> VALspec_range_exp_address_mapsto_eq by (exact H1).
  done.
 * unfold mapsto_, mapsto.
  rewrite H H0.
  rewrite -> if_false by auto.
  rewrite -> bi.pure_True by (split; [apply tc_val'_Vundef | auto]).
  rewrite -> Z2Nat.id by (pose proof (size_chunk_pos ch); lia).
  by rewrite bi.True_and.
Qed.

Lemma nonreadable_memory_block_mapsto: forall sh b ofs t ch v,
  ~ readable_share sh ->
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  tc_val' t v ->
  memory_block sh (size_chunk ch) (Vptr b ofs) ⊣⊢ mapsto sh t (Vptr b ofs) v.
Proof.
  intros.
  rewrite -mapsto__memory_block; eauto.
  rewrite /mapsto_ /mapsto.
  rewrite H0 H1 !if_false; try done.
  rewrite !bi.pure_True; try done.
  split; [apply tc_val'_Vundef | done].
Qed.*)

Lemma memory_block_eq': forall sh (n : nat) b ofs, 0 <= ofs -> ofs + n <= Ptrofs.max_unsigned ->
  memory_block' sh n b ofs ⊢ if readable_share_dec sh then VALspec_range n sh (b, ofs)
    else nonlock_permission_bytes sh (b,ofs) n.
Proof.
  intros.
  rewrite memory_block'_eq /memory_block'_alt //.
  if_tac; last done.
  rewrite /VALspec_range Nat2Z.id.
  apply big_sepL_mono; intros.
  iIntros "$".
  { unfold Ptrofs.max_unsigned in *; lia. }
Qed.

Lemma mapsto__memory_block: forall sh b ofs t ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  memory_block sh (size_chunk ch) (Vptr b ofs) ⊢ mapsto sh t (Vptr b ofs) Vundef.
Proof.
  intros.
  unfold mapsto_, mapsto, memory_block.
  iIntros "(% & H)".
  rewrite H H0 memory_block'_eq /memory_block'_alt.
  if_tac.
  - iSplit; first by iPureIntro; apply tc_val'_Vundef.
    rewrite /address_mapsto.
    iExists (repeat Undef (Z.to_nat (size_chunk ch))); iSplit.
    + rewrite repeat_length.
      iPureIntro; split3; try done.
      pose proof (size_chunk_pos ch).
      destruct (Z.to_nat (size_chunk ch)) eqn: ?; first lia.
      rewrite /decode_val /=.
      destruct ch; done.
    + rewrite (big_sepL_seq (repeat _ _)) repeat_length.
      by setoid_rewrite nth_repeat.
  - rewrite Z2Nat.id; last by pose proof (size_chunk_pos ch); lia.
    iFrame; iPureIntro; split; last done; split; last done.
    apply tc_val'_Vundef.
  - apply Ptrofs.unsigned_range.
  - rewrite Z2Nat.id; last by pose proof (size_chunk_pos ch); lia.
    lia.
Qed.

Lemma mapsto_share_join:
 forall sh1 sh2 sh t p v,
   sepalg.join sh1 sh2 sh ->
   mapsto sh1 t p v ∗ mapsto sh2 t p v ⊣⊢ mapsto sh t p v.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t) eqn:?; try solve [rewrite bi.False_sep; auto].
  destruct (type_is_volatile t) eqn:?; try solve [rewrite bi.False_sep; auto].
  destruct p; try solve [rewrite bi.False_sep; auto].
  destruct (readable_share_dec sh1), (readable_share_dec sh2);
    try rewrite -> (if_true (readable_share sh)) by (eapply join_sub_readable; [unfold sepalg.join_sub; eauto | auto]).
  + rewrite sepcon_andp_prop' sepcon_andp_prop assoc andp_dup; f_equiv.
    rewrite address_mapsto_share_join //.
  + rewrite sepcon_andp_prop' sepcon_andp_prop assoc -pure_and.
    rewrite (address_mapsto_align _ _ sh) (and_comm _ (_ ∧ _)) -assoc -pure_and and_comm; f_equiv.
    rewrite comm nonlock_permission_bytes_address_mapsto_join //.
    by apply sepalg.join_comm.
    { f_equiv; tauto. }
  + rewrite -> (if_true (readable_share sh)) by (eapply join_sub_readable; [unfold sepalg.join_sub; eexists; apply sepalg.join_comm; eauto | auto]).
    rewrite sepcon_andp_prop' sepcon_andp_prop assoc -pure_and.
    rewrite (address_mapsto_align _ _ sh) (and_comm _ (_ ∧ _)) -!assoc -pure_and and_comm; f_equiv.
    rewrite nonlock_permission_bytes_address_mapsto_join //.
    { f_equiv; tauto. }
  + rewrite -> if_false by (eapply join_unreadable_shares; eauto).
    rewrite -(nonlock_permission_bytes_share_join _ _ _ _ _ H); auto.
    rewrite sepcon_andp_prop' sepcon_andp_prop assoc andp_dup //.
Qed.

Lemma mapsto_share_joins:
 forall sh1 sh2 t p v,
   mapsto sh1 t p v ∗ mapsto sh2 t p v ⊢ ⌜sepalg.joins sh1 sh2⌝.
Proof.
  intros.
  unfold mapsto.
  iIntros "[H1 H2]".
  destruct (access_mode t) eqn:?; try done.
  destruct (type_is_volatile t) eqn:?; try done.
  destruct p; try done.
  destruct (readable_share_dec sh1), (readable_share_dec sh2).
  + iDestruct "H1" as (?) "H1"; iDestruct "H2" as (?) "H2".
    by iApply (address_mapsto_share_joins with "[$H1 $H2]").
  + iDestruct "H1" as (?) "H1"; iDestruct "H2" as (?) "H2".
    iDestruct (nonlock_permission_bytes_address_mapsto_joins with "[$H1 $H2]") as %?; iPureIntro; by apply psepalg.joins_comm.
  + iDestruct "H1" as (?) "H1"; iDestruct "H2" as (?) "H2".
    by iApply (nonlock_permission_bytes_address_mapsto_joins with "[$H1 $H2]").
  + iDestruct "H1" as "(% & H1)"; iDestruct "H2" as "(% & H2)".
    iApply (nonlock_permission_bytes_share_joins with "[$H1 $H2]").
    apply size_chunk_pos.
Qed.

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' ⊢ mapsto_ sh t v.
Proof. unfold mapsto_; intros; eauto. Qed.

Lemma memory_block_share_joins:
  forall sh1 sh2 n p, n > 0 ->
   memory_block sh1 n p ∗ memory_block sh2 n p ⊢ ⌜sepalg.joins sh1 sh2⌝.
Proof.
  intros.
  unfold memory_block.
  iIntros "[H1 H2]".
  destruct p; try done.
  destruct (Z.to_nat n) eqn: Hn; simpl; first lia.
  iDestruct "H1" as (_) "(H1 & _)"; iDestruct "H2" as (_) "(H2 & _)".
  if_tac; if_tac; rewrite ?address_mapsto_undef.
  + by iApply (address_mapsto_share_joins with "[$H1 $H2]").
  + iDestruct (nonlock_permission_bytes_address_mapsto_joins with "[$H1 $H2]") as %?; iPureIntro; by apply psepalg.joins_comm.
  + by iApply (nonlock_permission_bytes_address_mapsto_joins with "[H1 $H2]").
  + by iApply (nonlock_permission_bytes_share_joins with "[$H1 $H2]").
Qed.

Lemma mapsto_pure_facts: forall sh t p v,
  mapsto sh t p v ⊢ ⌜(exists ch, access_mode t = By_value ch) /\ isptr p⌝.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try iIntros "[]".
  destruct (type_is_volatile t); try iIntros "[]".
  destruct p; try iIntros "[]".
  iIntros "_"; iPureIntro; simpl; eauto.
Qed.

Lemma mapsto_overlap: forall sh {cs: compspecs} t1 t2 p1 p2 v1 v2
  (Hsh : sh <> Share.bot), pointer_range_overlap p1 (Ctypes.sizeof t1) p2 (Ctypes.sizeof t2) ->
  mapsto sh t1 p1 v1 ∗ mapsto sh t2 p2 v2 ⊢ False.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t1) eqn:AM1; try iIntros "[[] _]".
  destruct (access_mode t2) eqn:AM2; try iIntros "[_ []]".
  destruct (type_is_volatile t1); try iIntros "[[] _]".
  destruct (type_is_volatile t2); try iIntros "[_ []]".
  destruct p1; try iIntros "[[] _]".
  destruct p2; try iIntros "[_ []]".
  destruct H as (? & ? & H1 & H2 & H); simpl in *; subst.
  erewrite -> !size_chunk_sizeof in H by eauto.
  apply range_overlap_comm in H.
  if_tac.
  + iIntros "((_ & H1) & (_ & H2))".
    iApply address_mapsto_overlap; eauto with iFrame.
  + iIntros "[[% H] [% ?]]".
    iApply nonlock_permission_bytes_overlap; eauto with iFrame.
Qed.

Lemma memory_block_overlap: forall sh p1 n1 p2 n2 (Hsh : sh <> Share.bot), pointer_range_overlap p1 n1 p2 n2 -> memory_block sh n1 p1 ∗ memory_block sh n2 p2 ⊢ False.
Proof.
  intros.
  unfold memory_block.
  destruct p1; try iIntros "[[] _]".
  destruct p2; try iIntros "[_ []]".
  iIntros "[[% H] [% H2]]".
  destruct (pointer_range_overlap_non_zero _ _ _ _ H).
  destruct H as (? & ? & ? & ? & H%range_overlap_comm); simpl in *; subst.
  rewrite !memory_block_eq'.
  if_tac.
  + iApply (VALspec_range_overlap with "[$H $H2]").
    apply range_overlap_comm; rewrite !Z2Nat.id //; lia.
  + iApply (nonlock_permission_bytes_overlap with "[$]"); first done.
    rewrite !Z2Nat.id; auto; lia.
  + apply Ptrofs.unsigned_range.
  + rewrite Z2Nat.id /Ptrofs.max_unsigned; lia.
  + apply Ptrofs.unsigned_range.
  + rewrite Z2Nat.id /Ptrofs.max_unsigned; lia.
Qed.

Lemma mapsto_conflict:
  forall {cs : compspecs} sh t v v2 v3 (Hsh : sh <> Share.bot),
  mapsto sh t v v2 ∗ mapsto sh t v v3 ⊢ False.
Proof.
  intros.
  iIntros "[H1 H2]".
  iDestruct (mapsto_pure_facts with "H1") as %[[??] ?].
  assert (Ctypes.sizeof t > 0).
  { destruct t; try discriminate; simpl; try destruct i; try destruct f; try simple_if_tac; lia. }
  iApply (mapsto_overlap _ (cs := cs) with "[$]"); first done.
  apply pointer_range_overlap_refl; auto.
Qed.

Lemma memory_block_conflict: forall sh n m p (Hsh : sh <> Share.bot),
  0 < n <= Ptrofs.max_unsigned -> 0 < m <= Ptrofs.max_unsigned ->
  memory_block sh n p ∗ memory_block sh m p ⊢ False.
Proof.
  intros.
  destruct p; try iIntros "[[] _]".
  apply memory_block_overlap; first done.
  exists (b, Ptrofs.unsigned i), (b, Ptrofs.unsigned i); split3; try done.
  exists (b, Ptrofs.unsigned i).
  simpl; repeat split; auto; lia.
Qed.

Lemma memory_block_non_pos_Vptr: forall sh n b z, n <= 0 -> memory_block sh n (Vptr b z) = emp.
Proof.
  intros. unfold memory_block.
  rewrite -> Z_to_nat_neg by auto.
  unfold memory_block'.
  rewrite prop_true_andp //.
  pose proof Ptrofs.unsigned_range z. lia.
Qed.

Lemma memory_block_zero_Vptr: forall sh b z, memory_block sh 0 (Vptr b z) = emp.
Proof.
  intros; apply memory_block_non_pos_Vptr.
  lia.
Qed.

Lemma memory_block'_split:
  forall sh b ofs i j,
   0 <= i <= j ->
    j <= j+ofs < Ptrofs.modulus ->
   memory_block' sh (Z.to_nat j) b ofs ⊣⊢
      memory_block' sh (Z.to_nat i) b ofs ∗ memory_block' sh (Z.to_nat (j-i)) b (ofs+i).
Proof.
  intros.
  rewrite !memory_block'_eq; try rewrite Z2Nat.id; try lia.
  rewrite /memory_block'_alt.
  rewrite -> !Z2Nat.id by lia.
  if_tac.
  + replace (Z.to_nat j) with (Z.to_nat i + Z.to_nat (j - i))%nat by lia.
    rewrite seq_app big_sepL_app; f_equiv.
    replace (0 + Z.to_nat i)%nat with (Z.to_nat i + 0)%nat by lia.
    rewrite -fmap_add_seq big_sepL_fmap; do 3 f_equiv.
    rewrite /adr_add /=; do 2 f_equiv; lia.
  + apply nonlock_permission_bytes_split2; lia.
Qed.

Lemma memory_block_split:
  forall (sh : share) (b : block) (ofs n m : Z),
  0 <= n ->
  0 <= m ->
  n + m <= n + m + ofs < Ptrofs.modulus ->
  memory_block sh (n + m) (Vptr b (Ptrofs.repr ofs)) ⊣⊢
  memory_block sh n (Vptr b (Ptrofs.repr ofs)) ∗
  memory_block sh m (Vptr b (Ptrofs.repr (ofs + n))).
Proof.
  intros.
  unfold memory_block.
  rewrite -> memory_block'_split with (i := n); [| lia |].
  2:{
    pose proof Ptrofs.unsigned_range (Ptrofs.repr ofs).
    pose proof Ptrofs.unsigned_repr_eq ofs.
    assert (ofs mod Ptrofs.modulus <= ofs) by (apply Z.mod_le; lia).
    lia.
  } 
  replace (n + m - n) with m by lia.
  replace (memory_block' sh (Z.to_nat m) b (Ptrofs.unsigned (Ptrofs.repr ofs) + n)) with
    (memory_block' sh (Z.to_nat m) b (Ptrofs.unsigned (Ptrofs.repr (ofs + n)))).
  2: {
    destruct (zeq m 0).
    + subst. reflexivity.
    + assert (ofs + n < Ptrofs.modulus) by lia.
      rewrite -> !Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia).
      reflexivity.
  }
  iSplit.
  + iIntros "(% & $ & $)"; iPureIntro; repeat (split; auto); try lia.
    rewrite Ptrofs.unsigned_repr_eq.
    assert ((ofs + n) mod Ptrofs.modulus <= ofs + n) by (apply Z.mod_le; lia).
    lia.
  + iIntros "[[% $] [% $]]"; iPureIntro; repeat (split; auto); try lia.
    rewrite Ptrofs.unsigned_repr_eq.
    assert (ofs mod Ptrofs.modulus <= ofs) by (apply Z.mod_le; lia).
    lia.
Qed.

Lemma memory_block_share_join:
  forall sh1 sh2 sh n p,
   sepalg.join sh1 sh2 sh ->
   memory_block sh1 n p ∗ memory_block sh2 n p ⊣⊢ memory_block sh n p.
Proof.
  intros.
  destruct p; try solve [unfold memory_block; rewrite bi.False_sep; auto].
  destruct (zle 0 n).
  2:{
    rewrite -> !memory_block_non_pos_Vptr by lia.
    by rewrite left_id.
  }
  unfold memory_block.
  destruct (zlt (Ptrofs.unsigned i + n) Ptrofs.modulus).
  + rewrite -> bi.pure_True by auto.
    rewrite !bi.True_and.
    repeat (rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | rewrite Z2Nat.id; lia]).
    unfold memory_block'_alt.
    destruct (readable_share_dec sh1), (readable_share_dec sh2).
    - rewrite -> if_true by (eapply readable_share_join; eauto).
      rewrite -big_sepL_sep; do 3 f_equiv.
      rewrite slice.mapsto_share_join //.
    - rewrite -> if_true by (eapply readable_share_join; eauto).
      rewrite /nonlock_permission_bytes Nat2Z.id -big_sepL_sep; do 3 f_equiv.
      rewrite if_false // mapsto_mapsto_no_share_join //.
    - rewrite -> if_true by (eapply readable_share_join; eauto).
      rewrite /nonlock_permission_bytes Nat2Z.id -big_sepL_sep; do 3 f_equiv.
      rewrite if_false // comm mapsto_mapsto_no_share_join //.
      by apply sepalg.join_comm.
    - rewrite if_false.
      * apply nonlock_permission_bytes_share_join; auto.
      * eapply join_unreadable_shares; eauto.
  + rewrite -> bi.pure_False by auto.
    by rewrite !bi.False_and bi.False_sep.
Qed.

Lemma mapsto_pointer_void:
  forall sh t a, 
   eqb_type (Tpointer t a) int_or_ptr_type = false ->
   eqb_type (Tpointer Tvoid a) int_or_ptr_type = false ->
   mapsto sh (Tpointer t a) = mapsto sh (Tpointer Tvoid a).
Proof.
intros.
unfold mapsto.
extensionality v1 v2.
unfold tc_val', tc_val. rewrite H H0.
reflexivity.
Qed.

Lemma mapsto_core_load: forall t ch sh v b o, access_mode t = By_value ch -> readable_share sh ->
  mapsto sh t (Vptr b o) v ⊢ core_load ch (b, Ptrofs.unsigned o) v.
Proof.
  unfold mapsto.
  intros; rewrite H.
  iIntros "H".
  destruct (type_is_volatile t); try done.
  rewrite -> if_true by auto.
  iDestruct "H" as (?) "H"; by iApply (assert_lemmas.mapsto_core_load with "H").
Qed.

(* Timeless *)
Lemma nonlock_permission_bytes_timeless sh l n : n > 0 -> Timeless (nonlock_permission_bytes sh l n).
Proof.
  intros; rewrite /nonlock_permission_bytes.
  apply big_sepL_timeless'.
  intros; if_tac; try apply _.
  apply bi.exist_timeless; intros; apply bi.and_timeless; try apply _.
  apply gen_heap.mapsto_timeless; done.
  { destruct (Z.to_nat _) eqn: Hn; try done; lia. }
Qed.

Global Instance mapsto_timeless sh t v1 v2 : Timeless (mapsto sh t v1 v2).
Proof.
  rewrite /mapsto.
  destruct (access_mode t); try apply _.
  destruct (type_is_volatile t); try apply _.
  destruct v1; try apply _.
  if_tac; try apply _.
  apply bi.and_timeless; first apply _.
  apply nonlock_permission_bytes_timeless, size_chunk_pos.
Qed.

Lemma memory_block'_timeless sh n b o : (n > 0)%nat -> Timeless (memory_block' sh n b o).
Proof.
  revert o; induction n; simpl; first lia; intros.
  destruct (gt_dec n O).
  - apply bi.sep_timeless; [|eauto].
    if_tac; first apply _.
    by apply nonlock_permission_bytes_timeless.
  - replace n with O by lia; rewrite bi.sep_emp.
    if_tac; first apply _.
    by apply nonlock_permission_bytes_timeless.
Qed.

Lemma memory_block_timeless sh z p : z > 0 -> Timeless (memory_block sh z p).
Proof.
  intros.
  destruct p; simpl; try apply _.
  apply bi.and_timeless; first apply _.
  apply memory_block'_timeless; lia.
Qed.

(* valid_pointer *)
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
  + iDestruct "H" as "(% & H)"; iApply (address_mapsto_valid_pointer1 with "H"); rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
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
  + rewrite (big_sepL_lookup_acc _ _ (Z.to_nat i)); last by apply lookup_seq; split; try lia.
    iDestruct "H" as "(H & _)"; rewrite /adr_add /=.
    assert (0 <= i <= Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
    rewrite Ptrofs.add_unsigned !Ptrofs.unsigned_repr //.
    rewrite Z.add_0_r Z2Nat.id; last lia.
    iLeft; iFrame.
    { unfold Ptrofs.max_unsigned; lia. }
  + iApply (nonlock_permission_bytes_valid_pointer with "H"); last done; rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
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
  + destruct (decide (i = n)).
    * rewrite (big_sepL_lookup_acc _ _ (Z.to_nat (i - 1))); last by apply lookup_seq; split; try lia.
      iDestruct "H" as "(H & _)"; rewrite /adr_add /=.
      assert (0 <= i <= Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
      rewrite Ptrofs.add_unsigned !Ptrofs.unsigned_repr //.
      iRight; simpl.
      replace (Ptrofs.unsigned (Ptrofs.repr (Ptrofs.unsigned i0 + i)) + -1) with (Ptrofs.unsigned i0 + Z.to_nat (i - 1)).
      iLeft; iFrame.
      { rewrite Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
    * rewrite (big_sepL_lookup_acc _ _ (Z.to_nat i)); last by apply lookup_seq; split; try lia.
      iDestruct "H" as "(H & _)"; rewrite /adr_add /=.
      iLeft; simpl.
      assert (0 <= i <= Ptrofs.max_unsigned) by (unfold Ptrofs.max_unsigned; lia).
      rewrite Ptrofs.add_unsigned !Ptrofs.unsigned_repr //.
      rewrite Z.add_0_r Z2Nat.id; last lia.
      iLeft; iFrame.
      { unfold Ptrofs.max_unsigned; lia. }
  + iApply (nonlock_permission_bytes_weak_valid_pointer with "H"); last done; rewrite ?Ptrofs.unsigned_repr /Ptrofs.max_unsigned; lia.
Qed.

End mpred.
