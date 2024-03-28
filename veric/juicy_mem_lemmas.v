Require Import VST.veric.juicy_base.
Require Import VST.veric.res_predicates.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.shares.
Require Import VST.veric.Cop2.
Require Import VST.veric.mpred.

Local Close Scope Z.

Section mpred.

Context `{!heapGS Σ}.

Lemma perm_order'_trans: forall p1 p2 p3,
  perm_order' (Some p1) p2 -> perm_order' (Some p2) p3 -> perm_order' (Some p1) p3.
Proof.
intros.
unfold perm_order' in *.
eapply perm_order_trans; eauto.
Qed.

(* core load and coherence properties *)

Lemma core_load_coherent: forall ch v b ofs bl m,
  mem_auth m ∗ core_load' ch (b, ofs) v bl ⊢
  ⌜length bl = size_chunk_nat ch ∧ (align_chunk ch | ofs)%Z ∧ forall i, i < length bl -> exists sh, perm_order' (perm_of_dfrac sh) Readable ∧ coherent_loc m (b, ofs + Z.of_nat i)%Z (sh, Some (VAL (nthbyte i bl)))⌝.
Proof.
  intros; unfold core_load'.
  iIntros "(Hm & >((%H1 & _ & %H2) & H))".
  rewrite {1}H1; iSplit; first done; iSplit; first done.
  clear H1 H2; iInduction bl as [|?] "IH" forall (ofs); simpl in *.
  { iPureIntro; lia. }
  iDestruct "H" as "((% & %Hsh & H) & rest)".
  iDestruct (mapsto_lookup with "Hm H") as %[_ (Hloc & ? & ?)].
  iDestruct ("IH" with "Hm [rest]") as %Hrest.
  { iApply (big_sepL_mono with "rest"); intros.
    apply bi.exist_mono; intros.
    rewrite /adr_add /= Nat2Z.inj_succ /Z.succ (Z.add_comm _ 1) Z.add_assoc //. }
  iPureIntro; intros.
  destruct i; eauto.
  destruct (Hrest i); first lia.
  rewrite Nat2Z.inj_succ /Z.succ (Z.add_comm _ 1) Z.add_assoc.
  rewrite /nthbyte Z2Nat.inj_add; eauto; lia.
Qed.

Lemma getN_lookup : forall n z m i, (getN n z m !! i)%stdpp = if lt_dec i n then Some (Maps.ZMap.get (z + Z.of_nat i)%Z m) else None.
Proof.
  induction n; simpl; intros; first done.
  destruct i; simpl.
  - rewrite Z.add_0_r //.
  - rewrite IHn; if_tac; if_tac; auto; try lia.
    rewrite Nat2Z.inj_succ /Z.succ (Z.add_comm (Z.of_nat i) 1) Z.add_assoc //.
Qed.

Lemma core_load_getN: forall ch v b ofs bl m,
  mem_auth m ∗ core_load' ch (b, ofs) v bl ⊢
  ⌜bl = Mem.getN (size_chunk_nat ch) ofs (Maps.PMap.get b (Mem.mem_contents m))⌝.
Proof.
  intros.
  rewrite core_load_coherent; iIntros ((Hlen & _ & H)); iPureIntro.
  apply list_eq; intros.
  rewrite getN_lookup -Hlen.
  destruct (lt_dec i (length bl)).
  - destruct (H i) as (? & ? & Hi & _); first lia.
    rewrite /contents_cohere /contents_at /= in Hi.
    rewrite (Hi _ eq_refl).
    apply lookup_lt_is_Some_2 in l as [? Hbl].
    unfold nthbyte; erewrite nth_lookup_Some; eauto.
    rewrite Nat2Z.id //.
  - apply lookup_ge_None_2; lia.
Qed.

Lemma core_load_valid: forall ch v b ofs m,
  mem_auth m ∗ core_load ch (b, ofs) v ⊢
  ⌜Mem.valid_access m ch b ofs Readable⌝.
Proof.
  intros.
  iIntros "(Hm & >(% & H))".
  iDestruct (core_load_coherent with "[-]") as %(Hlen & Halign & H).
  { rewrite /core_load'; iFrame. }
  iPureIntro.
  rewrite /valid_access.
  split; auto.
  intros z Hz.
  rewrite size_chunk_conv -Hlen in Hz.
  destruct (H (Z.to_nat (z - ofs))) as (? & Hsh & _ & Hloc); first lia.
  rewrite Z2Nat.id /access_cohere in Hloc; last lia.
  rewrite Zplus_minus in Hloc.
  rewrite perm_access; eapply perm_order''_trans; eauto; simpl.
  destruct x as [[|]|]; done.
Qed.

Lemma core_load_load': forall ch b ofs v m,
  mem_auth m ∗ core_load ch (b, ofs) v ⊢ ⌜Mem.load ch m b ofs = Some v⌝.
Proof.
  intros.
  iIntros "H".
  iDestruct (core_load_valid with "H") as %[? Hload]%valid_access_load.
  rewrite Hload; apply load_result in Hload; subst.
  iDestruct "H" as "(Hm & % & >H)".
  iDestruct (core_load_getN with "[-]") as %?.
  { rewrite /core_load'; iFrame. }
  iDestruct "H" as "((% & <- & %) & H)"; subst; done.
Qed.

Lemma mapsto_coherent: forall ch v sh b ofs m,
  mem_auth m ∗ address_mapsto ch v sh (b, ofs) ⊢
  ⌜∃ bl, length bl = size_chunk_nat ch ∧ decode_val ch bl = v ∧ (align_chunk ch | ofs)%Z ∧ forall i, 0 <= i < size_chunk_nat ch -> coherent_loc m (b, ofs + Z.of_nat i)%Z (DfracOwn (Share sh), Some (VAL (nthbyte i bl)))⌝.
Proof.
  intros; unfold address_mapsto.
  iIntros "[Hm H]".
  iDestruct "H" as (bl (? & ? & ?)) "H".
  iExists bl; do 3 (iSplit; first done).
  rewrite -(big_opL_fmap VAL (fun i v => mapsto (adr_add (b, ofs) i) (DfracOwn (Share sh)) v)).
  iDestruct (mapsto_lookup_big with "Hm H") as %Hcoh; iPureIntro.
  rewrite -H; intros; specialize (Hcoh i).
  rewrite fmap_length list_lookup_fmap in Hcoh.
  destruct (lookup_lt_is_Some_2 bl i) as [? Hi]; first lia.
  rewrite Hi in Hcoh; rewrite /nthbyte Nat2Z.id (nth_lookup_Some _ _ _ _ Hi).
  apply Hcoh; lia.
Qed.

Lemma mapsto_valid_access_wr: forall ch v sh (wsh: writable0_share sh) b ofs m,
  mem_auth m ∗ address_mapsto ch v sh (b, ofs) ⊢
  ⌜Mem.valid_access m ch b ofs Writable⌝.
Proof.
  intros; rewrite mapsto_coherent; iIntros ((bl & Hlen & ? & ? & Hcoh)); iPureIntro.
  split; auto.
  intros z Hz.
  rewrite size_chunk_conv -Hlen in Hz.
  destruct (Hcoh (Z.to_nat (z - ofs))) as (_ & Hloc); first lia.
  rewrite Z2Nat.id /access_cohere in Hloc; last lia.
  rewrite Zplus_minus in Hloc.
  rewrite perm_access; eapply perm_order''_trans; eauto; simpl.
  rewrite /perm_of_sh if_true; last done.
  if_tac; constructor.
Qed.


Lemma mapsto_can_store: forall ch v sh (wsh: writable0_share sh) b ofs m v',
  mem_auth m ∗ address_mapsto ch v sh (b, ofs) ⊢
  ⌜exists m', Mem.store ch m b ofs v' = Some m'⌝.
Proof.
  intros.
  rewrite mapsto_valid_access_wr; last done.
  iIntros (H); iPureIntro.
  apply (valid_access_store _ _ _ _ v') in H as []; eauto.
Qed.

Definition decode_encode_val_ok (chunk1 chunk2: memory_chunk) : Prop :=
  match chunk1, chunk2 with
  | Mint8signed, Mint8signed => True
  | Mint8unsigned, Mint8signed => True
  | Mint8signed, Mint8unsigned => True
  | Mint8unsigned, Mint8unsigned => True
  | Mint16signed, Mint16signed => True
  | Mint16unsigned, Mint16signed => True
  | Mint16signed, Mint16unsigned => True
  | Mint16unsigned, Mint16unsigned => True
  | Mint32, Mfloat32 => True
  | Many32, Many32 => True
  | Many64, Many64 => True
  | Mint32, Mint32 => True
  | Mint64, Mint64 => True
  | Mint64, Mfloat64 => True
  | Mfloat64, Mfloat64 =>  True
  | Mfloat64, Mint64 =>  True
  | Mfloat32, Mfloat32 =>  True
  | Mfloat32, Mint32 =>  True
  | _,_ => False
  end.

Lemma decode_encode_val_ok_same:  forall ch,
    decode_encode_val_ok ch ch.
Proof.
destruct ch; simpl; auto.
Qed.

Lemma decode_encode_val_ok1:
  forall v ch ch' v',
 decode_encode_val_ok ch ch' ->
 decode_encode_val v ch ch' v' ->
 decode_val ch' (encode_val ch v) = v'.
Proof.
intros.
destruct ch, ch'; try contradiction;
destruct v; auto;
simpl in H0; subst;
unfold decode_val, encode_val;
try rewrite proj_inj_bytes;
rewrite -> ?decode_encode_int_1, ?decode_encode_int_2,
  ?decode_encode_int_4,
  ?decode_encode_int_8;
f_equal;
rewrite -> ?Int.sign_ext_zero_ext by reflexivity;
rewrite -> ?Int.zero_ext_sign_ext by reflexivity;
rewrite -> ?Int.zero_ext_idem by (compute; congruence);
auto.
all: try solve [
simpl; destruct Archi.ptr64; simpl; auto;
rewrite -> proj_sumbool_is_true by auto;
rewrite -> proj_sumbool_is_true by auto;
simpl; auto].
apply Float32.of_to_bits.
apply Float.of_to_bits.
Qed.

Lemma decode_encode_val_size:
  forall ch1 ch2, decode_encode_val_ok ch1 ch2 ->
   size_chunk ch1 = size_chunk ch2.
Proof.
intros.
destruct ch1, ch2; try contradiction;
simpl in *; subst; auto.
Qed.

Lemma mapsto_store': forall m ch ch' v v' sh b ofs m' (Hsh : writable0_share sh)
  (Hdec : decode_encode_val_ok ch ch') (Halign : (align_chunk ch' | ofs)%Z),
  Mem.store ch m b ofs v' = Some m' ->
  mem_auth m ∗ address_mapsto ch v sh (b, ofs) ⊢
  |==> mem_auth m' ∗ ∃ v'', ⌜decode_encode_val v' ch ch' v''⌝ ∧ address_mapsto ch' v'' sh (b, ofs).
Proof.
  intros.
  apply store_storebytes in H.
  iIntros "[Hm H]"; rewrite /address_mapsto.
  iDestruct "H" as (? (Hlen & <- & ?)) "H".
  iMod (mapsto_storebytes _ (b, ofs) _ (encode_val ch v') with "Hm H") as "[$ H]"; try assumption.
  { rewrite encode_val_length //. }
  iIntros "!>"; iExists _; iSplit; first by iPureIntro; apply decode_encode_val_general.
  iExists _; iFrame.
  iPureIntro; rewrite encode_val_length; repeat split; try done.
  { rewrite /size_chunk_nat (decode_encode_val_size _ _ Hdec) //. }
Qed.

Lemma decode_encode_val_fun:
  forall ch1 ch2, decode_encode_val_ok ch1 ch2 ->
  forall v v1 v2,
     decode_encode_val v ch1 ch2 v1 ->
     decode_encode_val v ch1 ch2 v2 ->
     v1=v2.
Proof.
intros.
destruct ch1, ch2; try contradiction;
destruct v; simpl in *; subst; auto.
Qed.

Lemma mapsto_store: forall m ch v v' sh b ofs m' (Hsh : writable0_share sh)
  t (Htc : tc_val' t v') (Hch : Ctypes.access_mode t = Ctypes.By_value ch),
  Mem.store ch m b ofs v' = Some m' ->
  mem_auth m ∗ address_mapsto ch v sh (b, ofs) ⊢
  |==> mem_auth m' ∗ address_mapsto ch v' sh (b, ofs).
Proof.
  intros.
  rewrite address_mapsto_align.
  iIntros "[Hm [H %]]".
  pose proof (decode_encode_val_ok_same ch).
  iMod (mapsto_store' with "[$]") as "($ & % & %Hv'' & H)"; [done..|].
  eapply decode_encode_val_fun in Hv'' as <-; try done.
  destruct (eq_dec v' Vundef); first by subst.
  specialize (Htc n).
  destruct t; try done; simpl in *.
  + unfold is_int in *.
    destruct v'; try done.
    destruct i, s; inv Hch; simpl in *; rewrite ?val_lemmas.sign_ext_inrange ?val_lemmas.zero_ext_inrange //;
      destruct Htc; subst; by compute.
  + inv Hch; destruct v'; done.
  + destruct f; inv Hch; destruct v'; done.
  + inv Hch; destruct (_ && _), v'; done.
Qed.

Local Open Scope Z.

Lemma store_outside':
   forall ch m b z v m',
          Mem.store ch m b z v = Some m' ->
  (forall b' ofs,
    (b=b' /\ z <= ofs < z + size_chunk ch) \/
     contents_at m (b', ofs) = contents_at m' (b', ofs))
  /\ access_at m = access_at m'
  /\ Mem.nextblock m = Mem.nextblock m'.
Proof.
intros.
repeat split.
intros.
generalize (Mem.store_mem_contents _ _ _ _ _ _ H); intro.
destruct (eq_block b b').
subst b'.
assert (z <= ofs < z + size_chunk ch \/ (ofs < z \/ ofs >= z + size_chunk ch)) by lia.
destruct H1.
left; auto.
right.
unfold contents_at; rewrite H0; clear H0.
simpl.
rewrite Maps.PMap.gss.
rewrite Mem.setN_other; auto.
intros.
rewrite encode_val_length in H0.
rewrite <- size_chunk_conv in H0.
destruct H0.
destruct H1.
lia.
lia.
right.
unfold contents_at; rewrite H0; clear H0.
simpl.
rewrite -> Maps.PMap.gso by auto. auto.
unfold access_at.  extensionality loc k.
f_equal.
symmetry; eapply Mem.store_access; eauto.
symmetry; eapply Mem.nextblock_store; eauto.
Qed.

Lemma adr_range_zle_zlt : forall  b lo hi ofs,
  adr_range (b,lo) (hi-lo) (b,ofs)
  -> zle lo ofs && zlt ofs hi = true.
Proof.
intros.
destruct H as [H [H1 H2]].
rewrite andb_true_iff.
split.
unfold zle.
case_eq (Z_le_gt_dec lo ofs); intros; auto.
unfold zlt.
case_eq (Z_lt_dec ofs hi); intros; auto.
lia.
Qed.

Lemma join_top: forall sh2 sh, sepalg.join Share.top sh2 sh -> sh = Share.top.
Proof.
intros. destruct H. rewrite Share.lub_commute Share.lub_top in H0. auto.
Qed.

Lemma replicate_repeat: forall {A} n (x : A), replicate n x = repeat x n.
Proof.
  induction n; auto; simpl.
  intros; rewrite IHn //.
Qed.

Lemma mapsto_alloc_bytes: forall m lo hi m' b,
  Mem.alloc m lo hi = (m', b) ->
  mem_auth m ⊢ |==> mem_auth m' ∗ [∗ list] i ∈ seq 0 (Z.to_nat (hi - lo)), address_mapsto Mint8unsigned Vundef Tsh (b, lo + Z.of_nat i).
Proof.
  intros.
  iIntros "Hm"; iMod (mapsto_alloc with "Hm") as "[$ H]"; first done.
  rewrite /address_mapsto.
  iApply (big_sepL_mono with "H"); intros ?? [-> ?]%lookup_seq.
  iIntros "?"; iExists [Undef]; simpl.
  rewrite /adr_add Z.add_0_r; iFrame.
  iPureIntro; repeat split; auto.
  apply Z.divide_1_l.
Qed.

Lemma mapsto_alloc: forall m ch lo hi m' b
  (Hch : size_chunk ch = hi - lo) (Halign : (align_chunk ch | lo)%Z),
  Mem.alloc m lo hi = (m', b) ->
  mem_auth m ⊢ |==> mem_auth m' ∗ address_mapsto ch Vundef Tsh (b, lo).
Proof.
  intros.
  iIntros "Hm"; iMod (mapsto_alloc with "Hm") as "[$ H]"; first done.
  rewrite /address_mapsto.
  iExists (replicate (Z.to_nat (hi - lo)) Undef).
  rewrite (big_sepL_seq (replicate _ _)) replicate_length; setoid_rewrite nth_replicate; iFrame.
  iPureIntro; split; last done.
  split; first by rewrite -Hch.
  split; last done.
  destruct (Z.to_nat _) eqn: ?; first by pose proof (size_chunk_pos ch); lia.
  rewrite /= decode_val_undef //.
Qed.

Lemma big_sepL_exist : forall {A B} `{base.Inhabited B} (f : nat -> A -> B -> mpred) l, ([∗ list] k↦v ∈ l, ∃ x, f k v x) ⊣⊢ ∃ lx, ⌜length lx = length l⌝ ∧ [∗ list] k↦v ∈ l, f k v (nth k lx inhabitant).
Proof.
  intros; revert f; induction l; simpl; intros.
  { iSplit; last eauto.
    iIntros "_"; iExists nil; done. }
  rewrite IHl.
  iSplit.
  - iIntros "((%x & ?) & (%lx & % & ?))".
    iExists (x :: lx); simpl; iFrame; auto.
  - iIntros "(%lx & %Hlen & Hx & ?)".
    iSplitL "Hx"; first eauto.
    destruct lx as [| ? lx]; inv Hlen; simpl.
    iExists lx; iFrame; done.
Qed.

Lemma big_opL_seq_index : forall {M : ofe} (o : M -> M -> M) `{Monoid _ o} n (f : nat -> nat -> M), (([^o list] k↦v ∈ seq 0 n, f k v) ≡ [^o list] v ∈ seq 0 n, f v v)%stdpp.
Proof.
  intros.
  apply big_opL_proper.
  intros ??[-> _]%lookup_seq; done.
Qed.

Lemma big_sepL_seq_exist : forall {A} `{base.Inhabited A} (f : nat -> A -> mpred) n, ([∗ list] i ∈ seq 0 n, ∃ x, f i x) ⊣⊢ ∃ lx, ⌜length lx = n⌝ ∧ [∗ list] k↦v ∈ lx, f k v.
Proof.
  intros.
  rewrite big_sepL_exist.
  apply bi.exist_proper; intros lx.
  rewrite seq_length (big_sepL_seq lx) big_opL_seq_index.
  iSplit; iIntros "[-> ?]"; iFrame; done.
Qed.

Lemma VALspec_range_perm: forall m n sh l p, perm_of_sh sh = Some p ->
  mem_auth m ∗ VALspec_range n sh l ⊢
  ⌜Mem.range_perm m l.1 l.2 (l.2 + n) Cur p⌝.
Proof.
  intros.
  iIntros "(Hm & H)".
  iIntros (a ?).
  rewrite /VALspec_range (big_sepL_lookup_acc _ _ (Z.to_nat (a - l.2))).
  2: { apply lookup_seq; split; eauto; lia. }
  iDestruct "H" as "[H _]".
  rewrite /VALspec /adr_add /=.
  iDestruct "H" as (?) "H".
  replace (l.2 + Z.to_nat (a - l.2)) with a by lia.
  iDestruct (mapsto_lookup with "Hm H") as %(? & ? & _ & _ & Hacc); iPureIntro.
  rewrite /access_cohere /access_at /= H // in Hacc.
Qed.

Lemma VALspec_range_can_free: forall m n l,
  mem_auth m ∗ VALspec_range n Share.top l ⊢
  ⌜∃ m', free m l.1 l.2 (l.2 + n) = Some m'⌝.
Proof.
  intros.
  rewrite VALspec_range_perm; last apply perm_of_freeable.
  apply bi.pure_mono; intros.
  apply range_perm_free in H as [??]; eauto.
Qed.

Lemma mapsto_can_free: forall m ch v l,
  mem_auth m ∗ address_mapsto ch v Share.top l ⊢
  ⌜∃ m', free m l.1 l.2 (l.2 + size_chunk ch) = Some m'⌝.
Proof.
  intros.
  rewrite address_mapsto_VALspec_range; apply VALspec_range_can_free.
Qed.

Lemma VALspec_range_free: forall m b lo hi m',
  Mem.free m b lo hi = Some m' ->
  mem_auth m ∗ VALspec_range (hi - lo) share_top (b, lo) ⊢ |==> mem_auth m'.
Proof.
  intros.
  iIntros "[Hm H]".
  rewrite /VALspec_range /VALspec.
  rewrite big_sepL_seq_exist.
  iDestruct "H" as (? Hlen) "H".
  rewrite -(big_sepL_fmap _ (fun i b0 => adr_add (b, lo) i ↦ b0)).
  iApply (mapsto_free with "Hm H"); first done.
  rewrite fmap_length Hlen //.
Qed.

Lemma mapsto_free: forall m ch b lo hi m' v (Hch : size_chunk ch = hi - lo),
  Mem.free m b lo hi = Some m' ->
  mem_auth m ∗ address_mapsto ch v Tsh (b, lo) ⊢ |==> mem_auth m'.
Proof.
  intros.
  rewrite address_mapsto_VALspec_range Hch.
  apply VALspec_range_free; done.
Qed.

End mpred.
