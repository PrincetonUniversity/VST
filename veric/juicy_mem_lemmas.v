Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.wsat.
Require Import VST.veric.res_predicates.
Require Import VST.veric.shares.
Require Import VST.veric.Cop2.

Section mpred.

Context `{!heapGS Σ}.

(*
(*Lemma inflate_initial_mem_empty:
  forall lev, emp (inflate_initial_mem Mem.empty lev).
intro lev.
unfold inflate_initial_mem.
destruct (make_rmap (inflate_initial_mem' Mem.empty lev) (core (ghost_of lev))
        (inflate_initial_mem'_valid Mem.empty lev) (level lev)
        (inflate_initial_mem'_fmap Mem.empty lev)); simpl.
{ rewrite core_ghost_of, <- level_core; apply ghost_of_approx. }
destruct a.
apply resource_at_empty2.
intro l; rewrite H0.
unfold inflate_initial_mem'.
destruct l.
unfold access_at; unfold empty at 1.
simpl.
rewrite PMap.gi.
destruct (max_access_at empty (b,z)); try destruct p; try apply NO_identity.
Qed.
Local Hint Resolve inflate_initial_mem_empty : core.*)

(* TODO: move this somewhere more appropriate *)
Definition no_VALs (phi: rmap) := forall loc,
  match phi @ loc with
    | YES _ _ (VAL _) _ => False | _ => True
  end.

Lemma perm_of_sh_join_sub: forall (sh1 sh2: Share.t) p,
  perm_of_sh sh1 = Some p ->
  join_sub sh1 sh2 ->
  perm_order' (perm_of_sh sh2) p.
Proof.
intros.
destruct H0.
unfold perm_of_sh in *.
repeat if_tac in H; inv H.
+
inv H0. rewrite Share.glb_commute, Share.glb_top in H; subst x.
 rewrite (Share.lub_bot).
rewrite if_true by auto. rewrite if_true by auto. constructor.
+ apply join_writable01 in H0 ;auto. rewrite if_true by auto.
  if_tac; constructor.
+ apply join_readable1 in H0; auto.
  if_tac. if_tac; constructor. rewrite if_true by auto. constructor.
+ assert (sh2 <> Share.bot). contradict H3.
  apply split_identity in H0; auto. apply identity_share_bot; auto.
  subst; auto.
  repeat if_tac; try constructor. contradiction.
Qed.*)

Lemma perm_order'_trans: forall p1 p2 p3,
  perm_order' (Some p1) p2 -> perm_order' (Some p2) p3 -> perm_order' (Some p1) p3.
Proof.
intros.
unfold perm_order' in *.
eapply perm_order_trans; eauto.
Qed.

(* core load and coherence properties *)

(*Lemma writable_perm:
  forall b i jm, writable (b,i) (m_phi jm) -> Mem.perm (m_dry jm) b i Cur Writable.
Proof.
intros until jm; intros H.
assert (Hacc := juicy_mem_access jm).
unfold access_cohere in Hacc.
unfold Mem.perm, Mem.perm_order'.
specialize ( Hacc (b, i)).
simpl in H.
destruct (m_phi jm @ (b, i)).
contradiction.
destruct H as [H1 H2]. destruct k; inv H2.
unfold access_at in Hacc.
simpl in Hacc.
rewrite Hacc.
clear - H1.
simpl.
unfold perm_of_sh. rewrite if_true by auto. if_tac; constructor.
contradiction.
Qed.

Lemma valid_access_None: forall m ch b b' ofs ofs' p,
  Mem.valid_access m ch b ofs p
  -> adr_range (b, ofs) (size_chunk ch) (b', ofs')
  -> access_at m (b', ofs') Cur = None
  -> False.
Proof.
unfold access_at, Mem.valid_access, Mem.perm, Mem.range_perm, Mem.perm, Mem.perm_order'.
simpl.
intros.
destruct H as [H ?].
destruct H0 as [H3 H4].
subst.
specialize( H ofs' H4).
rewrite H1 in H.
auto.
Qed.*)

Lemma core_load_coherent: forall ch v b ofs bl m,
  mem_auth m ∗ core_load' ch (b, ofs) v bl ⊢
  ⌜length bl = size_chunk_nat ch ∧ (align_chunk ch | ofs)%Z ∧ forall i, i < length bl -> exists sh, perm_order' (perm_of_dfrac sh) Readable ∧ coherent_loc(V := leibnizO resource) m (b, ofs + Z.of_nat i)%Z (Some (sh, Some (VAL (nthbyte i bl))))⌝.
Proof.
  intros; unfold core_load'.
  iIntros "(Hm & >((%H1 & _ & %H2) & H))".
  rewrite {1}H1; iSplit; first done; iSplit; first done.
  clear H1 H2; iInduction bl as [|?] "IH" forall (ofs); simpl in *.
  { iPureIntro; lia. }
  iDestruct "H" as "((% & %Hsh & H) & rest)".
  iDestruct (mapsto_lookup with "Hm H") as %[_ Hloc].
  iDestruct ("IH" with "Hm [rest]") as %H.
  { iApply (big_sepL_mono with "rest"); intros.
    apply bi.exist_mono; intros.
    rewrite /adr_add /= Nat2Z.inj_succ /Z.succ (Z.add_comm _ 1) Z.add_assoc //. }
  iPureIntro; intros.
  destruct Hloc, i; eauto.
  destruct (H i); first lia.
  rewrite Nat2Z.inj_succ /Z.succ (Z.add_comm _ 1) Z.add_assoc.
  rewrite /nthbyte Z2Nat.inj_add; eauto; lia.
Qed.

Lemma getN_lookup : forall n z m i, getN n z m !! i = if lt_dec i n then Some (Maps.ZMap.get (z + Z.of_nat i)%Z m) else None.
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
  destruct (H (Z.to_nat (z - ofs))) as (? & Hsh & _ & Hloc & _); first lia.
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

(*Lemma Zminus_lem: forall z1 z2, z1 <= z2 -> Z.to_nat (z2 - z1) = O -> z1=z2.
Proof. lia. Qed.

Lemma nat_of_Z_lem1: forall n z, 
    S n = Z.to_nat z -> n = Z.to_nat (z - 1).
Proof. lia. Qed.

Lemma nat_of_Z_lem2: forall n z1 z2, S n = Z.to_nat (z1 - z2) -> n = Z.to_nat (z1 - z2 - 1).
Proof. intros; apply nat_of_Z_lem1; auto. Qed.

Lemma nth_getN: forall m b ofs ofs' z,
  ofs <= ofs' < ofs + z
  -> z >= 0
  -> contents_at m (b, ofs')
  = nth (Z.to_nat (ofs' - ofs)) (Mem.getN (Z.to_nat z) ofs (PMap.get b (Mem.mem_contents m))) Undef.
Proof.
intros.
revert ofs ofs' H H0.
remember (Z.to_nat z) as n.
revert n z Heqn.
induction n; intros.
destruct z.
inv H.
lia.
simpl in *.
generalize (lt_O_nat_of_P p). intro.
lia.
generalize (Zlt_neg_0 p).
intro.
lia.
simpl.
case_eq (Z.to_nat (ofs' - ofs)).
intros.
assert (ofs = ofs').
  destruct H.
  apply Zminus_lem; auto.
subst; auto.
intros.
symmetry in H1.
assert (n = Z.to_nat (z - 1)) by (apply nat_of_Z_lem1 in Heqn; auto).
rewrite (IHn (z - 1) H2 (ofs + 1)); try solve [auto|lia].
assert (Z.to_nat (ofs' - (ofs + 1)) = n0).
replace (ofs' - (ofs + 1)) with (ofs' - ofs - 1) by lia.
  apply nat_of_Z_lem1 in H1.
  auto.
rewrite H3; auto.
Qed.*)

(* When would we need to generate a core_load assertion while already knowing the resources in a state?
Lemma load_core_load: forall ch b ofs v m,
  Mem.load ch (m_dry m) b ofs = Some v ->
  mem_auth m ∗ ([∗ list] z ∈ seq 0 (size_chunk_nat ch), ⌜coherent_loc m 

forall z, ofs <= z < ofs + size_chunk ch ->
                      perm_order'' (perm_of_res (m_phi m @ (b,z))) (Some Readable)) ->
   ⊢ mem_auth m ∗ core_load ch (b, ofs) v.
Proof.
intros until m; intros H PERM.
hnf.
unfold Mem.load in H.

if_tac in H; try solve [inv H].
inversion H.
clear H.
exists (Mem.getN (size_chunk_nat ch) ofs (PMap.get b (Mem.mem_contents (m_dry m)))).
generalize H0 as H0'; intro.
Local Hint Resolve Mem.getN_length : core.
unfold Mem.valid_access in H0'.
destruct H0' as [H0'1 H0'2].
repeat split; auto.
clear H0'1 H0'2.
intros (b', ofs').
hnf.
if_tac; hnf; auto.
assert (Heqbb': b = b').
  unfold adr_range in H. decompose [and] H. auto.
pose proof (juicy_mem_contents m).
pose proof I. (* pose proof (juicy_mem_access m).*)
pose proof I.
pose proof I.
clear H4. subst b'; clear H5.
destruct H as [_ ?].
specialize (PERM ofs' H).
(*
unfold access_cohere in H3.
specialize (H3 (b, ofs').
*)
unfold perm_of_res in *.
destruct H0 as [H0 _].
specialize (H0 ofs').
specialize (H0 H).
hnf in H0.
(*unfold access_at in H3.
simpl in H3.
*)
destruct ((mem_access (m_dry m)) !! b ofs' Cur); try contradiction.
destruct (m_phi m @ (b, ofs')) eqn:H8; try contradiction.
if_tac in PERM; inv PERM.
destruct k; try now inv PERM.
pose proof (size_chunk_pos ch).
rewrite <- nth_getN with (ofs := ofs) (z := size_chunk ch); auto; try lia.
exists sh, r.
destruct (H1 _ _ _ _ _ H8); subst.
f_equal.
inv PERM.
Qed.

Lemma core_load_load: forall ch b ofs v m,
  (forall z, ofs <= z < ofs + size_chunk ch ->
                      perm_order'' (perm_of_res (m_phi m @ (b,z))) (Some Readable)) ->
  (core_load ch (b, ofs) v (m_phi m) <-> Mem.load ch (m_dry m) b ofs = Some v).
Proof.
intros.
split; [apply core_load_load'| ].
intros; apply load_core_load; auto.
Qed.*)

(*Lemma address_mapsto_exists':
  forall ch v sh (rsh: readable_share sh) loc m lev,
      (align_chunk ch | snd loc)
      -> Mem.load ch m (fst loc) (snd loc) = Some v 
      -> exists w, address_mapsto ch v sh loc w /\ level w = lev.
Proof.
intros. rename H into Halign.
unfold address_mapsto.
pose (f l' := if adr_range_dec loc (size_chunk ch) l'
                     then YES sh rsh (VAL (nthbyte (snd l' - snd loc) (Mem.getN (size_chunk_nat ch) (snd loc) (PMap.get (fst loc) (Mem.mem_contents m))))) NoneP
                     else NO Share.bot bot_unreadable).
assert (CompCert_AV.valid (res_option oo f)).
apply VAL_valid.
unfold compose, f; intros.
if_tac in H.
simpl in H.
injection H;intros; subst k; auto.
inv H.
destruct (make_rmap f H lev) as [phi [? ?]].
extensionality l; unfold f, compose; simpl.
if_tac; hnf; auto.
exists phi.
split; auto.
exists (Mem.getN (size_chunk_nat ch) (snd loc) (PMap.get (fst loc) (Mem.mem_contents m))).
split.
repeat split; auto.
Transparent Mem.load.
unfold load in *. if_tac in H0. injection H0. auto. inv H0.
intro l'.
unfold jam.
hnf.
simpl.
rewrite H2; clear H H1 H2.
unfold f; clear f.
if_tac.
exists rsh.
f_equal. 
apply NO_identity.
Qed.*)

(*Lemma mapsto_valid_access: forall ch v sh b ofs m,
  mem_auth m ∗ address_mapsto ch v sh (b, ofs) ⊢
  ⌜Mem.valid_access m ch b ofs Readable⌝.
Proof.
  Search address_mapsto readable_share.
core_load_valid
intros.
unfold address_mapsto in H.
unfold Mem.valid_access, Mem.range_perm.
split.
destruct H as [x [y [Hjoin ?]]].
destruct H as [[bl [[H2 [H3 H3']] H]] ?].
hnf in H.
intros ofs' H4.
specialize (H (b, ofs')).
hnf in H.
destruct (adr_range_dec (b, ofs) (size_chunk ch) (b, ofs')) as [H5|H5].
  2: unfold adr_range in H5.
  2: exfalso; apply H5; split; auto.
hnf in H.
destruct H as [pf H].
hnf in H.
rewrite preds_fmap_NoneP in H.
simpl in H.
generalize (resource_at_join _ _ _ (b,ofs') Hjoin); rewrite H; intro.
forget ((nth (Z.to_nat (ofs' - ofs)) bl Undef)) as v'.
assert (exists rsh', exists sh', m_phi jm @ (b,ofs') = YES rsh' sh' (VAL v') NoneP).
inv H1; eauto.
destruct H6 as [rsh' [sh' ?]].
generalize (juicy_mem_access jm (b,ofs')); rewrite H6; unfold perm_of_res; simpl; intro.
clear - H7 sh'.
unfold perm, access_at in *.
simpl in H7.
forget ((mem_access (m_dry jm)) !! b ofs' Cur) as p1.
unfold perm_of_sh in H7.
if_tac in H7.
if_tac in H7; inv H7; constructor.
rewrite if_true in H7 by auto.
subst; constructor.
repeat match goal with [ H: context[ _ /\ _ ] |- _] => destruct H end.
auto.
Qed.*)

Lemma mapsto_coherent: forall ch v sh b ofs m,
  mem_auth m ∗ address_mapsto ch v sh (b, ofs) ⊢
  ⌜∃ bl, length bl = size_chunk_nat ch ∧ decode_val ch bl = v ∧ (align_chunk ch | ofs)%Z ∧ forall i, 0 <= i < size_chunk_nat ch -> coherent_loc(V := leibnizO resource) m (b, ofs + Z.of_nat i)%Z (Some (DfracOwn (Share sh), Some (VAL (nthbyte i bl))))⌝.
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
  destruct (Hcoh (Z.to_nat (z - ofs))) as (_ & Hloc & _); first lia.
  rewrite Z2Nat.id /access_cohere in Hloc; last lia.
  rewrite Zplus_minus in Hloc.
  rewrite perm_access; eapply perm_order''_trans; eauto; simpl.
  rewrite /perm_of_sh if_true; last done.
  if_tac; constructor.
Qed.

(*Search Mem.valid_access Mem.store.
Program Definition mapsto_can_store_definition ch v sh (wsh: writable0_share sh) b ofs m (v':val)
  (MAPSTO: (address_mapsto ch v sh (b, ofs) * TT)%pred (m_phi jm)):
  Memory.mem.
Proof. intros.
pose proof (mapsto_valid_access_wr _ _ _ wsh _ _ _ MAPSTO).
apply (mkmem
  (PMap.set b (setN (encode_val ch v') ofs (PMap.get b (mem_contents (m_dry jm))))
    (mem_contents (m_dry jm))) (mem_access (m_dry jm))
  (nextblock (m_dry jm)) (access_max (m_dry jm)) (nextblock_noaccess (m_dry jm))).
intros. destruct jm; simpl.
  rewrite PMap.gsspec. destruct (peq b0 b).
  rewrite setN_default. apply contents_default.
  apply contents_default.
Defined.

Lemma mapsto_can_store_property: forall (ch:memory_chunk) v sh (wsh: writable0_share sh) b ofs jm v'
  (MAPSTO: (address_mapsto ch v sh (b, ofs) * TT)%pred (m_phi jm)),
  Mem.store ch (m_dry jm) b ofs v' = 
  Some(mapsto_can_store_definition _ _ _ wsh _ _ jm v' MAPSTO).
Proof.
intros.
pose proof (mapsto_valid_access_wr _ _ _ wsh _ _ _ MAPSTO).
unfold mapsto_can_store_definition. simpl.
Transparent Mem.store. unfold store.
destruct (valid_access_dec (m_dry jm) ch b ofs Writable).
f_equal. f_equal; auto with extensionality.
contradiction.
Opaque Mem.store.
Qed.*)

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
  rewrite -(big_opL_fmap VAL (fun i v => mapsto (adr_add (b, ofs) i) (DfracOwn (Share sh)) v)).
  iMod (mapsto_storebytes _ _ (b, ofs) _ (VAL <$> encode_val ch v') with "Hm H") as "[$ H]".
  { rewrite Forall2_lookup; intros.
    rewrite list_lookup_fmap; destruct (_ !! _); constructor; done. }
  { rewrite Forall2_lookup; intros.
    rewrite !list_lookup_fmap.
    destruct (lt_dec i (length bl)).
    * destruct (lookup_lt_is_Some_2 _ _ l) as [? ->].
      rewrite Hlen -(encode_val_length ch v') in l.
      destruct (lookup_lt_is_Some_2 _ _ l) as [? ->]; constructor.
      intros; apply perm_order''_refl.
    * rewrite lookup_ge_None_2; last lia.
      rewrite lookup_ge_None_2; first constructor.
      rewrite encode_val_length -Hlen; lia. }
  iIntros "!>"; iExists _; iSplit; first by iPureIntro; apply decode_encode_val_general.
  rewrite big_opL_fmap; iExists _; iFrame.
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
  iMod (mapsto_store' with "[$]") as "($ & % & %Hv'' & H)".
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
  iIntros "Hm"; iMod (mapsto_alloc _ _ _ _ _ (VAL Undef) with "Hm") as "[$ H]"; first done.
  rewrite /address_mapsto.
  rewrite -fmap_replicate big_sepL_fmap big_sepL_seq replicate_length.
  iApply (big_sepL_mono with "H"); intros ?? [-> ?]%lookup_seq.
  iIntros "?"; iExists [Undef]; simpl.
  rewrite replicate_repeat nth_repeat /adr_add Z.add_0_r; iFrame.
  iPureIntro; repeat split; auto.
  apply Z.divide_1_l.
Qed.

Lemma mapsto_alloc: forall m ch lo hi m' b
  (Hch : size_chunk ch = hi - lo) (Halign : (align_chunk ch | lo)%Z),
  Mem.alloc m lo hi = (m', b) ->
  mem_auth m ⊢ |==> mem_auth m' ∗ address_mapsto ch Vundef Tsh (b, lo).
Proof.
  intros.
  iIntros "Hm"; iMod (mapsto_alloc _ _ _ _ _ (VAL Undef) with "Hm") as "[$ H]"; first done.
  rewrite /address_mapsto.
  rewrite -fmap_replicate big_sepL_fmap.
  iExists _; iFrame; iPureIntro.
  split; last done.
  split; first by rewrite replicate_length -Hch.
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

Lemma big_sepL_seq_index : forall n (f : nat -> nat -> mpred), ([∗ list] k↦v ∈ seq 0 n, f k v) ⊣⊢ [∗ list] v ∈ seq 0 n, f v v.
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
  rewrite seq_length (big_sepL_seq lx) big_sepL_seq_index.
  iSplit; iIntros "[-> ?]"; iFrame; done.
Qed.

Lemma VALspec_range_can_free: forall m n l,
  mem_auth m ∗ VALspec_range n Share.top l ⊢
  ⌜∃ m', free m l.1 l.2 (l.2 + n) = Some m'⌝.
Proof.
  intros.
  iIntros "(Hm & H)".
  iAssert ⌜range_perm m l.1 l.2 (l.2 + n) Cur Freeable⌝ as %H; last by iPureIntro; apply range_perm_free in H as [??]; eauto.
  iIntros (??).
  rewrite /VALspec_range (big_sepL_lookup_acc _ _ (Z.to_nat (a - l.2))).
  2: { apply lookup_seq; split; eauto; lia. }
  iDestruct "H" as "[H _]".
  rewrite /VALspec /adr_add /=.
  iDestruct "H" as (?) "H".
  replace (l.2 + Z.to_nat (a - l.2)) with a by lia.
  iDestruct (mapsto_lookup with "Hm H") as %(? & ? & _ & Hacc & _); iPureIntro.
  rewrite /access_cohere /access_at /= perm_of_freeable -mem_lemmas.po_oo // in Hacc.
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
  mem_auth m ∗ VALspec_range (hi - lo) Tsh (b, lo) ⊢ |==> mem_auth m'.
Proof.
  intros.
  iIntros "[Hm H]".
  rewrite /VALspec_range /VALspec.
  rewrite big_sepL_seq_exist.
  iDestruct "H" as (? Hlen) "H".
  rewrite -(big_sepL_fmap _ (fun i b0 => adr_add (b, lo) i ↦ b0)).
  iApply (mapsto_free with "Hm H").
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

(*
Lemma writable_writable_after_alloc' : forall m1 m2 lo hi b lev loc IOK1 IOK2,
  alloc m1 lo hi = (m2, b) ->
  writable loc (m_phi (initial_mem m1 lev IOK1)) ->
  writable loc (m_phi (initial_mem m2 lev IOK2)).
Proof.
intros.
hnf in *.
case_eq (m_phi (initial_mem m1 lev IOK1) @ loc); intros.
rewrite H1 in H0.
inv H0.
rewrite H1 in H0.
assert (~adr_range (b,lo) (hi-lo) loc). {
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) loc).
  destruct loc. simpl in *.
  rewrite H1 in Ha.
  destruct H0 as [_ H0]. destruct k; inv H0.
  intro Contra.
  destruct Contra.
  subst.
  assert (access_at m1 (nextblock m1, z) Cur = None).
    unfold access_at; apply nextblock_noaccess; simpl. apply Plt_strict.
  assert (b0 = nextblock m1) by (eapply alloc_result; eauto).
  subst.
  rewrite Ha in H0. simpl in H0. clear - r H0.
  unfold perm_of_sh in H0. repeat if_tac in H0; try contradiction; inv H0.
}
apply alloc_dry_unchanged_on with (m1:=m1)(m2:=m2) in H2; auto.
destruct H2.
unfold initial_mem; simpl.
unfold inflate_initial_mem, inflate_initial_mem'.
rewrite resource_at_make_rmap.
destruct loc as (b',ofs').
assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) (b',ofs')). {
  rewrite H1 in Ha.
  destruct H0 as [Hfree H0]. destruct k; try solve [inversion H0].
  unfold perm_of_res in Ha. simpl in Ha.
  rewrite <- H3.
  rewrite <- H2. rewrite Ha.
  clear - Hfree r.
  unfold perm_of_sh. rewrite if_true by auto. if_tac; auto.
  rewrite Ha. unfold perm_of_sh. rewrite if_true by auto. 
  clear; if_tac; congruence.
 }
 rewrite H1 in H0. simpl in H0. contradiction.
Qed.

Lemma readable_eq_after_alloc' : forall m1 m2 lo hi b lev loc IOK1 IOK2,
  alloc m1 lo hi = (m2, b) ->
  readable loc (m_phi (initial_mem m1 lev IOK1)) ->
  m_phi (initial_mem m1 lev IOK1) @ loc=m_phi (initial_mem m2 lev IOK2) @ loc.
Proof.
intros.
hnf in H0.
case_eq (m_phi (initial_mem m1 lev IOK1) @ loc); intros.
rewrite H1 in H0.
inv H0.
rewrite H1 in H0.
assert (~adr_range (b,lo) (hi-lo) loc). {
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) loc).
  destruct loc. simpl in *.
  rewrite H1 in Ha.
  destruct k; try solve [inv H0].
  intro Contra.
  destruct Contra.
  subst.
  assert (b0 = nextblock m1) by (eapply alloc_result; eauto).
  subst.
  simpl in Ha.
(*
  destruct (perm_of_sh_pshare t p) as [p' H4].
  unfold perm_of_res in Ha; simpl in Ha; rewrite H4 in Ha.
*)
  assert (access_at m1 (nextblock m1, z) Cur = None).
    unfold access_at. simpl. apply nextblock_noaccess. apply Plt_strict.
  rewrite H2 in Ha.
  clear - Ha r. unfold perm_of_sh in Ha. repeat if_tac in Ha; inv Ha; try contradiction.
}
apply alloc_dry_unchanged_on with (m1:=m1)(m2:=m2) in H2; auto.
destruct H2.
rewrite <- H1.
unfold initial_mem; simpl.
unfold inflate_initial_mem, inflate_initial_mem'.
do 2 rewrite resource_at_make_rmap.
destruct loc as (b',ofs').
 assert (Ha := juicy_mem_access (initial_mem m1 lev IOK1) (b',ofs')). {
   rewrite H1 in Ha.   unfold perm_of_res in Ha; simpl in Ha.
   simpl in H0. destruct k; try contradiction.
  rewrite <- H2. rewrite Ha in *.
  spec H3. clear - r. unfold perm_of_sh. repeat if_tac; try congruence; contradiction.
  rewrite <- H3.
  unfold perm_of_sh. if_tac. if_tac; auto. rewrite if_true by auto. auto.

 }
 rewrite H1 in H0. contradiction.
Qed.

Lemma perm_order''_trans p1 p2 p3 :
  perm_order'' p1 p2 ->
  perm_order'' p2 p3 ->
  perm_order'' p1 p3.
Proof.
  destruct p1, p2, p3; simpl; try tauto.
  apply perm_order_trans.
Qed.

Lemma po_join_sub_sh sh1 sh2 :
  join_sub sh2 sh1 ->
  Mem.perm_order'' (perm_of_sh sh1) (perm_of_sh sh2).
Proof.
  intros [sh J].
  unfold perm_of_sh.
  if_tac. if_tac. repeat if_tac; constructor.
  if_tac. rewrite if_false. constructor.
  contradict H0. subst. apply join_top in J; auto.
  repeat if_tac; constructor.
  assert (~writable0_share sh2) by (contradict H; eapply join_writable01; eauto).
  if_tac. rewrite if_false by auto. repeat if_tac; constructor.
  rewrite (if_false (writable0_share sh2)) by auto.
  assert (~readable_share sh2) by (contradict H1; eapply join_readable1; eauto).
  rewrite (if_false (readable_share sh2)) by auto.
  if_tac.
  subst. apply split_identity in J. apply identity_share_bot in J.
  rewrite if_true by auto. constructor.
  auto. if_tac; constructor.
Qed.

Lemma po_join_sub r1 r2 :
  join_sub r2 r1 ->
  Mem.perm_order'' (perm_of_res r1) (perm_of_res r2).
Proof.
  intros. destruct H as [r J]. inv J; simpl.
  if_tac. subst. apply split_identity in RJ.
  apply identity_share_bot in RJ. rewrite if_true by auto; constructor.
  auto. if_tac; constructor.
  destruct k; try constructor; apply po_join_sub_sh; eexists; eauto.
  apply perm_order''_trans with (Some Nonempty).
  destruct k; try constructor.
  unfold perm_of_sh. if_tac. if_tac; constructor. rewrite if_true by auto; constructor.
  if_tac; constructor.
  destruct k; try constructor. apply po_join_sub_sh; eexists; eauto.
  constructor.
Qed.

(*
Lemma po_join_sub' r1 r2 :
  join_sub r2 r1 ->
  Mem.perm_order'' (perm_of_res' r1) (perm_of_res' r2).
Proof.
  
*)
Lemma perm_of_res_lock_not_Freeable:
  forall r,
    perm_order'' (Some Writable) (perm_of_res_lock r).
Proof.
  intros.
  unfold perm_of_res_lock.
  destruct r; try constructor.
  destruct k; try constructor.
  unfold perm_of_sh.
  if_tac. rewrite if_false. constructor.
  apply glb_Rsh_not_top.
  repeat if_tac; constructor.
Qed.

Definition readable_perm (p: option permission) :
  {perm_order'' p (Some Readable)}+{~perm_order'' p (Some Readable)}.
destruct p.
destruct p; try solve [left; constructor].
all: right; intro; inv H.
Defined.

Definition rebuild_juicy_mem_fmap (jm: juicy_mem) (m': mem) : (AV.address -> resource) :=
 fun loc =>
   match m_phi jm @ loc with
    PURE k pp => PURE k pp
   | NO sh rsh => if readable_perm (access_at m' loc Cur)
                            then YES Tsh (writable_readable writable_share_top)
                                        (VAL (contents_at m' loc)) NoneP
                            else NO sh rsh 
   | YES sh rsh (VAL _) _ => 
                 if readable_perm (access_at m' loc Cur)
                 then YES sh rsh (VAL (contents_at m' loc)) NoneP
                 else NO _ bot_unreadable
   | YES sh rsh _ _ => m_phi jm @ loc
end.

Definition rebuild_juicy_mem_rmap (jm: juicy_mem) (m': mem) :
  {phi : rmap |
  level phi = level jm /\
  resource_at phi = rebuild_juicy_mem_fmap jm m' /\
  ghost_of phi = ghost_of (m_phi jm)}.
  refine (make_rmap (rebuild_juicy_mem_fmap jm m') (ghost_of (m_phi jm)) (level jm) _ _).
extensionality loc.
unfold compose.
unfold rebuild_juicy_mem_fmap.
destruct (m_phi jm @ loc) eqn:?H.
if_tac; auto.
pose proof (resource_at_approx (m_phi jm) loc).
rewrite H in H0. simpl in H0.
destruct k; simpl; auto.
if_tac; auto.
pose proof (resource_at_approx (m_phi jm) loc).
rewrite H in *; auto.
apply ghost_of_approx.
Defined.*)

End mpred.
