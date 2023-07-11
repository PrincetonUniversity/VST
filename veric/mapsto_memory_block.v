Require Import VST.veric.base.
Require Import VST.veric.res_predicates.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.assert_lemmas.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.address_conflict.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.Cop2.
Require Import VST.veric.shares.
Require Import VST.veric.slice.

Require Import VST.veric.mpred.

Section mpred.

Context `{!heapGS Σ}.

(*Lemma address_mapsto_exists:
  forall ch v sh (rsh: readable_share sh) loc w0
      (RESERVE: forall l', adr_range loc (size_chunk ch) l' -> w0 @ l' = NO Share.bot bot_unreadable),
      (align_chunk ch | snd loc) ->
      exists w, address_mapsto ch (decode_val ch (encode_val ch v)) sh loc w 
                    /\ core w = core w0.
Proof.  exact address_mapsto_exists. Qed.*)

Definition permission_block (sh: Share.t)  (v: val) (t: type) : mpred :=
    match access_mode t with
         | By_value ch =>
            match v with
            | Vptr b ofs =>
                 nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs)
                       (size_chunk ch)
            | _ => False
            end
         | _ => False
         end.

Definition mapsto (sh: Share.t) (t: type) (v1 v2 : val): mpred :=
  match access_mode t with
  | By_value ch =>
   match type_is_volatile t with
   | false =>
    match v1 with
     | Vptr b ofs =>
       if readable_share_dec sh
       then (⌜tc_val t v2⌝ ∧
             address_mapsto ch v2 sh (b, Ptrofs.unsigned ofs)) ∨
            (⌜v2 = Vundef⌝ ∧
             ∃ v2':val, address_mapsto ch v2' sh (b, Ptrofs.unsigned ofs))
       else ⌜tc_val' t v2 /\ (align_chunk ch | Ptrofs.unsigned ofs)⌝ ∧ nonlock_permission_bytes sh (b, Ptrofs.unsigned ofs) (size_chunk ch)
     | _ => False
    end
    | _ => False
    end
  | _ => False
  end.

Definition mapsto_ sh t v1 := mapsto sh t v1 Vundef.

(*Lemma address_mapsto_readable:
  forall m v sh a, address_mapsto m v sh a ⊢ 
           ⌜readable_share sh⌝.
Proof.
intros.
unfold address_mapsto.
unfold derives.
simpl.
intros ? ?.
destruct H as [bl [[? [? ?]]] ].
specialize (H2 a).
rewrite if_true in H2.
destruct H2 as [rsh ?]. auto.
destruct a; split; auto.
clear; pose proof (size_chunk_pos m); lia.
Qed.*)

Lemma mapsto_tc_val': forall sh t p v, mapsto sh t p v ⊢ ⌜tc_val' t v⌝.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  if_tac; auto;
  destruct p; auto;
  try simple_if_tac; auto.
  + iIntros "[[% H] | [-> H]]"; iPureIntro.
    - apply tc_val_tc_val'; auto.
    - apply tc_val'_Vundef.
  + iIntros "[[$ _] _]".
Qed.

Lemma mapsto_value_range:
 forall sh v sz sgn i
   (Hsh : readable_share sh),
   mapsto sh (Tint sz sgn noattr) v (Vint i) ⊢
    ⌜int_range sz sgn i⌝.
Proof.
intros.
rewrite mapsto_tc_val'; iIntros "%"; iPureIntro.
hnf in H.
spec H; first done.
simpl in H.
unfold int_range.
assert (MAX: Int.max_signed = 2147483648 - 1) by reflexivity.
assert (MIN: Int.min_signed = -2147483648) by reflexivity.
assert (Byte.min_signed = -128) by reflexivity.
assert (Byte.max_signed = 128-1) by reflexivity.
assert (Byte.max_unsigned = 256-1) by reflexivity.
destruct (Int.unsigned_range i).
assert (Int.modulus = Int.max_unsigned + 1) by reflexivity.
assert (Int.modulus = 4294967296) by reflexivity.
destruct sz, sgn; auto; try lia.
- split; [etrans | eapply Z.le_lt_trans]; try apply H; try lia; try by compute.
- split; try lia.
  eapply Z.le_lt_trans; [apply H | by compute].
- pose proof (Int.signed_range i); lia.
- destruct H; subst; by compute.
- destruct H; subst; by compute.
Qed.

Definition writable_block (id: ident) (n: Z): environ -> mpred :=
   fun rho => 
        ∃ b: block,  ∃ sh: Share.t,
          ⌜writable_share sh /\ ge_of rho id = Some b⌝ ∧ VALspec_range n sh (b, 0).

Fixpoint writable_blocks (bl : list (ident*Z)) : environ -> mpred :=
 match bl with
  | nil =>  fun rho => emp
  | (b,n)::bl' =>  fun rho => writable_block b n rho ∗ writable_blocks bl' rho
 end.

Fixpoint address_mapsto_zeros (sh: share) (n: nat) (adr: address) : mpred :=
 match n with
 | O => emp
 | S n' => address_mapsto Mint8unsigned (Vint Int.zero) sh adr 
               ∗ address_mapsto_zeros sh n' (fst adr, Z.succ (snd adr))
end.

Definition address_mapsto_zeros' (n: Z) : spec :=
     fun (sh: Share.t) (l: address) => [∗ list] i ∈ seq 0 (Z.to_nat n), adr_add l (Z.of_nat i) ↦{#sh} VAL (Byte Byte.zero).

Lemma address_mapsto_zeros_eq:
  forall sh n l,
   address_mapsto_zeros sh n l ⊣⊢
   address_mapsto_zeros' (Z_of_nat n) sh l.
Proof.
  induction n;
  destruct l as [b i].
  * (* base case *)
    reflexivity.
  * (* inductive case *)
    rewrite /= IHn /address_mapsto_zeros' !Nat2Z.id -cons_seq /= -seq_shift big_sepL_fmap.
    apply bi.sep_proper.
    - rewrite /address_mapsto /=.
      iSplit.
      + iIntros "H"; iDestruct "H" as ([| ? [|]] (? & Hz & ?)) "H"; simpl in *; try discriminate.
        replace m with (Byte Byte.zero); first by iDestruct "H" as "[$ _]".
        rewrite /decode_val /= in Hz.
        destruct m; try discriminate.
        f_equal; apply Byte.same_if_eq.
        assert (0 ≤ Byte.unsigned i0 ≤ Int.max_unsigned).
        { pose proof (Byte.unsigned_range i0) as Hi; split; try apply Hi.
          etrans; [apply Z.lt_le_incl, Hi | by compute]. }
        rewrite /decode_int rev_if_be_1 /= Z.add_0_r zero_ext_inrange in Hz.
        unfold Byte.eq; rewrite if_true; auto.
        { assert (Int.unsigned (Int.repr (Byte.unsigned i0)) = Int.unsigned Int.zero) as Heq by congruence.
          rewrite !Int.unsigned_repr in Heq; auto.
          by compute. }
        { rewrite Int.unsigned_repr; auto.
          etrans; [apply Byte.unsigned_range_2 | by compute]. }
      + iIntros "H"; iExists [Byte Byte.zero]; simpl; iFrame.
        iPureIntro; repeat split; auto.
        apply Z.divide_1_l.
    - apply big_sepL_proper; intros.
      rewrite /adr_add /= Nat2Z.inj_succ.
      by replace (Z.succ i + Z.of_nat y) with (i + Z.succ (Z.of_nat y)) by lia.
Qed.

Definition mapsto_zeros (n: Z) (sh: share) (a: val) : mpred :=
 match a with
  | Vptr b z => 
    ⌜0 <= Ptrofs.unsigned z  /\ n + Ptrofs.unsigned z < Ptrofs.modulus⌝ ∧
    address_mapsto_zeros sh (Z.to_nat n) (b, Ptrofs.unsigned z)
  | _ => False
  end.

Fixpoint memory_block' (sh: share) (n: nat) (b: block) (i: Z) : mpred :=
  match n with
  | O => emp
  | S n' => mapsto_ sh (Tint I8 Unsigned noattr) (Vptr b (Ptrofs.repr i))
         ∗ memory_block' sh n' b (i+1)
 end.

Definition memory_block'_alt (sh: share) (n: nat) (b: block) (ofs: Z) : mpred :=
 if readable_share_dec sh
 then VALspec_range (Z_of_nat n) sh (b, ofs)
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
    unfold mapsto_, mapsto.
    simpl access_mode. cbv beta iota.
    change (type_is_volatile (Tint I8 Unsigned noattr)) with false. cbv beta iota.
    if_tac.
    - rewrite -> (VALspec_range_split2 1 (Z_of_nat n) (Z.of_nat (S n))) by (try rewrite inj_S; lia).
      rewrite VALspec1.
      apply bi.sep_proper; last done.
      assert (i < Ptrofs.modulus) by (rewrite Nat2Z.inj_succ in H0; lia).
      rewrite -> Ptrofs.unsigned_repr by (unfold Ptrofs.max_unsigned; lia); clear H1.
      clear.
      iSplit.
      * iIntros "[[% H] | [_ H]]".
        { apply tc_val_Vundef in H; contradiction. }
        iDestruct "H" as (?) "H"; iPoseProof (address_mapsto_VALspec_range with "H") as "H".
        by rewrite /= VALspec1.
      * iIntros "H"; iRight; iSplit; first done.
        iApply VALspec_range_exp_address_mapsto; first apply Z.divide_1_l.
        by rewrite /= VALspec1.
    - rewrite -> (nonlock_permission_bytes_split2 1 (Z_of_nat n) (Z.of_nat (S n)))  by (try rewrite inj_S; lia).
      apply bi.sep_proper; last done.
      rewrite -> Ptrofs.unsigned_repr by (rewrite Nat2Z.inj_succ in H0; unfold Ptrofs.max_unsigned; lia).
      rewrite bi.pure_True.
      by rewrite bi.True_and.
      { split; [apply tc_val'_Vundef | apply Z.divide_1_l]. }
Qed.

Definition memory_block (sh: share) (n: Z) (v: val) : mpred :=
 match v with
 | Vptr b ofs => ⌜Ptrofs.unsigned ofs + n < Ptrofs.modulus⌝ ∧ memory_block' sh (Z.to_nat n) b (Ptrofs.unsigned ofs)
 | _ => False
 end.

Lemma mapsto__exp_address_mapsto: forall sh t b i_ofs ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  readable_share sh ->
  mapsto_ sh t (Vptr b i_ofs) ⊣⊢ ∃ v2' : val,
            address_mapsto ch v2' sh (b, (Ptrofs.unsigned i_ofs)).
Proof.
  intros.
  unfold mapsto_, mapsto.
  rewrite H H0.
  rewrite -> if_true by auto.
  rewrite -> bi.pure_False by apply tc_val_Vundef.
  rewrite bi.False_and bi.False_or bi.pure_True; last done.
  by rewrite bi.True_and.
Qed.

Lemma exp_address_mapsto_VALspec_range_eq:
  forall ch sh l,
    (∃ v: val, address_mapsto ch v sh l) ⊣⊢ ⌜(align_chunk ch | snd l)⌝ ∧ VALspec_range (size_chunk ch) sh l.
Proof.
  intros; iSplit.
  + iIntros "H"; iDestruct "H" as (?) "H".
    iSplit; last by iApply address_mapsto_VALspec_range.
    rewrite /address_mapsto.
    iDestruct "H" as (? (? & ? & ?)) "?"; auto.
  + iIntros "[% H]".
    iApply VALspec_range_exp_address_mapsto; auto.
Qed.

Lemma VALspec_range_exp_address_mapsto_eq:
  forall ch sh l,
    (align_chunk ch | snd l) ->
    VALspec_range (size_chunk ch) sh l ⊣⊢ ∃ v: val, address_mapsto ch v sh l.
Proof.
  intros.
  rewrite exp_address_mapsto_VALspec_range_eq bi.pure_True; last done.
  by rewrite bi.True_and.
Qed.

Lemma mapsto__memory_block: forall sh b ofs t ch,
  access_mode t = By_value ch ->
  type_is_volatile t = false ->
  (align_chunk ch | Ptrofs.unsigned ofs) ->
  Ptrofs.unsigned ofs + size_chunk ch < Ptrofs.modulus ->
  mapsto_ sh t (Vptr b ofs) ⊣⊢ memory_block sh (size_chunk ch) (Vptr b ofs).
Proof.
  intros.
  unfold memory_block.
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
Qed.

Lemma guarded_sep_or_distr : forall (P1 P2: Prop) (p1 p2 q1 q2 : mpred),
  (P1 -> P2 -> False) ->
  (⌜P1⌝ ∧ p1 ∨ ⌜P2⌝ ∧ p2) ∗ (⌜P1⌝ ∧ q1 ∨ ⌜P2⌝ ∧ q2) ⊣⊢ ⌜P1⌝ ∧ (p1 ∗ q1) ∨ ⌜P2⌝ ∧ (p2 ∗ q2).
Proof.
  intros.
  rewrite bi.sep_or_r.
  rewrite (bi.sep_comm (⌜P1⌝ ∧ p1)).
  rewrite (bi.sep_comm (⌜P2⌝ ∧ p2)).
  rewrite !bi.sep_or_r.
  iSplit.
  + iIntros "[[[[% ?] [% ?]] | [[% ?] [% ?]]] | [[[% ?] [% ?]] | [[% ?] [% ?]]]]"; try tauto.
    - by iLeft; iFrame.
    - by iRight; iFrame.
  + iIntros "[(% & ? & ?) | (% & ? & ?)]".
    - by iLeft; iLeft; iFrame.
    - by iRight; iRight; iFrame.
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
  + rewrite guarded_sep_or_distr; last by intros; subst; eapply tc_val_Vundef; eauto.
    apply bi.or_proper; first by rewrite address_mapsto_share_join.
    apply bi.and_proper; first done.
    rewrite bi.sep_exist_r; apply bi.exist_proper; intros v1.
    rewrite -(address_mapsto_share_join _ _ _ _ _ _ H); auto.
    iSplit.
    * iIntros "[H1 H2]"; iDestruct "H2" as (?) "H2".
      iDestruct (address_mapsto_value_cohere with "[$H1 $H2]") as %->; iFrame.
    * iIntros "[$ ?]"; eauto.
  + rewrite bi.sep_or_r.
    apply bi.or_proper; iSplit.
    * iIntros "[[% H1] [% H2]]".
      iCombine "H2 H1" as "?"; rewrite nonlock_permission_bytes_address_mapsto_join; auto.
      by apply sepalg.join_comm.
    * iIntros "[% H]".
      rewrite address_mapsto_align; iDestruct "H" as "[H %]".
      rewrite !bi.pure_True; auto.
      rewrite !bi.True_and comm nonlock_permission_bytes_address_mapsto_join; auto.
      { by apply sepalg.join_comm. }
      { split; auto; by apply tc_val_tc_val'. }
    * iIntros "[[$ H1] [% H2]]".
      iDestruct "H1" as (?) "H1".
      iCombine "H2 H1" as "?"; rewrite nonlock_permission_bytes_address_mapsto_join; auto.
      by apply sepalg.join_comm.
    * iIntros "[% H]".
      iDestruct "H" as (?) "H".
      rewrite address_mapsto_align; iDestruct "H" as "[H %]".
      rewrite !bi.pure_True; auto.
      rewrite !bi.True_and bi.sep_exist_r.
      iExists v2'; rewrite comm nonlock_permission_bytes_address_mapsto_join; auto.
      { by apply sepalg.join_comm. }
      { subst; split; auto; by apply tc_val'_Vundef. }
  + rewrite -> (if_true (readable_share sh)) by (eapply join_sub_readable; [unfold sepalg.join_sub; eexists; apply sepalg.join_comm; eauto | auto]).
    rewrite bi.sep_or_l.
    apply bi.or_proper; iSplit.
    * iIntros "[[% H1] [% H2]]".
      iCombine "H1 H2" as "?"; rewrite nonlock_permission_bytes_address_mapsto_join; auto.
    * iIntros "[% H]".
      rewrite address_mapsto_align; iDestruct "H" as "[H %]".
      rewrite !bi.pure_True; auto.
      rewrite !bi.True_and nonlock_permission_bytes_address_mapsto_join; auto.
      { split; auto; by apply tc_val_tc_val'. }
    * iIntros "[[% H1] [$ H2]]".
      iDestruct "H2" as (?) "H2".
      iCombine "H1 H2" as "?"; rewrite nonlock_permission_bytes_address_mapsto_join; auto.
    * iIntros "[% H]".
      iDestruct "H" as (?) "H".
      rewrite address_mapsto_align; iDestruct "H" as "[H %]".
      rewrite !bi.pure_True; auto.
      rewrite !bi.True_and bi.sep_exist_l.
      iExists v2'; rewrite nonlock_permission_bytes_address_mapsto_join; auto.
      { subst; split; auto; by apply tc_val'_Vundef. }
  + rewrite -> if_false by (eapply join_unreadable_shares; eauto).
    rewrite -(nonlock_permission_bytes_share_join _ _ _ _ _ H); auto.
    iSplit.
    * iIntros "[[$ $] [_ $]]".
    * iIntros "(% & $ & $)"; auto.
Qed.

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' ⊢ mapsto_ sh t v.
Proof. unfold mapsto_; intros.
  unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); auto.
  destruct v; auto.
  if_tac.
  + iIntros "[[% ?] | [% ?]]"; eauto.
  + iIntros "[[% %] $]"; iPureIntro; repeat split; auto.
    apply tc_val'_Vundef.
Qed.

(*Lemma mapsto_not_nonunit: forall sh t p v, ~ nonunit sh -> mapsto sh t p v ⊢ emp.
Proof.
  intros.
  unfold mapsto.
  destruct (access_mode t); try solve [apply False_derives].
  destruct (type_is_volatile t); try solve [apply False_derives].
  destruct p; try solve [apply False_derives].
  if_tac.
  + apply readable_nonidentity in H0.
    apply nonidentity_nonunit in H0; tauto.
  + apply andp_left2.
    apply nonlock_permission_bytes_not_nonunit; auto.
Qed.*)

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
  (Hsh : sh <> Share.bot), pointer_range_overlap p1 (sizeof t1) p2 (sizeof t2) ->
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
  + trans ((∃ v : val, address_mapsto m v sh (b, Ptrofs.unsigned i)) ∗
          (∃ v : val, address_mapsto m0 v sh (b0, Ptrofs.unsigned i0))).
    { apply bi.sep_mono; (iIntros "[[% H] | [% H]]"; [|iDestruct "H" as (?) "H"]); eauto. }
    iIntros "[H1 H2]"; iDestruct "H1" as (?) "H1"; iDestruct "H2" as (?) "H2".
    iApply address_mapsto_overlap; iFrame.
  + iIntros "[[% H] [% ?]]".
    iApply nonlock_permission_bytes_overlap; iFrame.
Qed.

Lemma Nat2Z_add_lt: forall n i, Ptrofs.unsigned i + n < Ptrofs.modulus ->
  Z.of_nat (Z.to_nat n) + Ptrofs.unsigned i < Ptrofs.modulus.
Proof.
  intros.
  destruct (zle 0 n).
  + rewrite -> Z2Nat.id by lia. lia.
  + rewrite -> Z2Nat_neg by lia.
    pose proof Ptrofs.unsigned_range i.
    simpl.
    lia.
Qed.

Lemma Nat2Z_add_le: forall n i, Ptrofs.unsigned i + n <= Ptrofs.modulus ->
  Z.of_nat (Z.to_nat n) + Ptrofs.unsigned i <= Ptrofs.modulus.
Proof.
  intros.
  destruct (zle 0 n).
  + rewrite -> Z2Nat.id by lia. lia.
  + rewrite -> Z2Nat_neg by lia.
    pose proof Ptrofs.unsigned_range i.
    simpl.
    lia.
Qed.

Lemma memory_block_overlap: forall sh p1 n1 p2 n2 (Hsh : sh <> Share.bot), pointer_range_overlap p1 n1 p2 n2 -> memory_block sh n1 p1 ∗ memory_block sh n2 p2 ⊢ False.
Proof.
  intros.
  unfold memory_block.
  destruct p1; try iIntros "[[] _]".
  destruct p2; try iIntros "[_ []]".
  iIntros "[[% H] [% ?]]".
  destruct (pointer_range_overlap_non_zero _ _ _ _ H).
  destruct H as (? & ? & ? & ? & H%range_overlap_comm); simpl in *; subst.
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | apply Nat2Z_add_lt; lia].
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i0; lia | apply Nat2Z_add_lt; lia].
  unfold memory_block'_alt.
  if_tac.
  + iApply (VALspec_range_overlap with "[$]").
    rewrite !Z2Nat.id; auto; lia.
  + iApply (nonlock_permission_bytes_overlap with "[$]").
    rewrite !Z2Nat.id; auto; lia.
Qed.

Lemma mapsto_conflict:
  forall {cs : compspecs} sh t v v2 v3 (Hsh : sh <> Share.bot),
  mapsto sh t v v2 ∗ mapsto sh t v v3 ⊢ False.
Proof.
  intros.
  iIntros "[H1 H2]".
  iDestruct (mapsto_pure_facts with "H1") as %[[??] ?].
  assert (sizeof t > 0).
  { destruct t; try discriminate; simpl; try destruct i; try destruct f; try simple_if_tac; lia. }
  iApply (mapsto_overlap _ (cs := cs) with "[$]").
  apply pointer_range_overlap_refl; auto.
Qed.

Lemma memory_block_conflict: forall sh n m p (Hsh : sh <> Share.bot),
  0 < n <= Ptrofs.max_unsigned -> 0 < m <= Ptrofs.max_unsigned ->
  memory_block sh n p ∗ memory_block sh m p ⊢ False.
Proof.
  intros.
  unfold memory_block.
  destruct p; try iIntros "[[] _]".
  iIntros "[[% H1] [% H2]]".
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | rewrite Z2Nat.id; lia].
  rewrite memory_block'_eq; [| pose proof Ptrofs.unsigned_range i; lia | rewrite Z2Nat.id; lia].
  unfold memory_block'_alt.
  if_tac.
  + iApply VALspec_range_overlap; last iFrame.
    exists (b, Ptrofs.unsigned i).
    simpl; repeat split; auto; try lia;
    rewrite Z2Nat.id; lia.
  + iApply nonlock_permission_bytes_overlap; last iFrame.
    exists (b, Ptrofs.unsigned i).
    repeat split; auto; try rewrite Z2Nat.id; lia.
Qed.

Lemma memory_block_non_pos_Vptr: forall sh n b z, n <= 0 -> memory_block sh n (Vptr b z) ⊣⊢ emp.
Proof.
  intros. unfold memory_block.
  rewrite -> Z_to_nat_neg by auto.
  unfold memory_block'.
  iSplit; auto; iIntros "_"; iPureIntro; split; auto.
  pose proof Ptrofs.unsigned_range z. lia.
Qed.

Lemma memory_block_zero_Vptr: forall sh b z, memory_block sh 0 (Vptr b z) ⊣⊢ emp.
Proof.
  intros; apply memory_block_non_pos_Vptr.
  lia.
Qed.

Lemma mapsto_zeros_memory_block: forall sh n p,
  mapsto_zeros n sh p ⊢
  memory_block sh n p.
Proof.
  intros.
  unfold mapsto_zeros, memory_block.
  destruct p; try iIntros "[]".
  iIntros "[% H]"; iSplit; [iPureIntro; lia|].
  destruct (zlt n 0).
  { rewrite -> Z_to_nat_neg by lia; done. }
  rewrite address_mapsto_zeros_eq memory_block'_eq; try (rewrite ?Z2Nat.id; lia).
  rewrite /address_mapsto_zeros' /memory_block'_alt.
  rewrite -> Z2Nat.id by lia.
  if_tac.
  - rewrite /VALspec_range /VALspec.
    iApply (big_sepL_mono with "H"); eauto.
  - rewrite /nonlock_permission_bytes.
    destruct (Z.to_nat n) eqn: ?; first done; simpl.
    iDestruct "H" as "[H ?]"; iDestruct (mapsto_valid with "H") as %[??]; done.
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
  + apply VALspec_range_split2; lia.
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
      apply VALspec_range_share_join; auto.
    - rewrite -> if_true by (eapply readable_share_join; eauto).
      rewrite comm.
      apply nonlock_permission_bytes_VALspec_range_join; auto.
      by apply sepalg.join_comm.
    - rewrite -> if_true by (eapply readable_share_join; eauto).
      apply nonlock_permission_bytes_VALspec_range_join; auto.
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

Lemma is_pointer_or_null_nullval: is_pointer_or_null nullval.
Proof.
unfold is_pointer_or_null, nullval.
simple_if_tac; auto.
Qed.
#[local] Hint Resolve is_pointer_or_null_nullval : core.

Lemma tc_val_pointer_nullval':
 forall t a, tc_val (Tpointer t a) nullval.
Proof.
 intros. hnf. unfold nullval.
 simple_if_tac; hnf;
 simple_if_tac; auto.
Qed.
#[local] Hint Resolve tc_val_pointer_nullval' : core.

Arguments type_is_volatile ty / .

Definition is_int32_noattr_type t :=
 match t with
 | Tint I32 _ {| attr_volatile := false; attr_alignas := None |} => True%type
 | _ => False%type
 end.

Lemma mapsto_mapsto_int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v ⊢ mapsto sh t2 p v.
Proof.
intros.
destruct t1; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
destruct t2; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
done.
Qed.

Lemma mapsto_mapsto__int32:
  forall sh t1 t2 p v,
   is_int32_noattr_type t1 ->
   is_int32_noattr_type t2 ->
   mapsto sh t1 p v ⊢ mapsto_ sh t2 p.
Proof.
intros.
destruct t1; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
destruct t2; try destruct i; try contradiction.
destruct a as [ [ | ] [ | ] ]; try contradiction.
unfold mapsto_. apply mapsto_mapsto_.
Qed.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh (Tint I32 Unsigned noattr) = mapsto sh (Tint I32 Signed noattr).
Proof.
intros.
extensionality v1 v2.
reflexivity.
Qed.

Lemma tc_val_pointer_nullval:
 forall t, tc_val (Tpointer t noattr) nullval.
Proof.
 intros. unfold nullval; simpl.
 rewrite andb_false_r.
 hnf. simple_if_tac; auto.
Qed.
#[local] Hint Resolve tc_val_pointer_nullval : core.

Lemma mapsto_tuint_tptr_nullval:
  forall sh p t, mapsto sh (Tpointer t noattr) p nullval ⊣⊢ mapsto sh size_t p nullval.
Proof.
intros.
unfold mapsto, size_t.
destruct p; try reflexivity.
destruct Archi.ptr64 eqn:Hp.
*
simpl access_mode; cbv beta iota.
simpl type_is_volatile; cbv beta iota.
unfold Mptr; rewrite Hp.
if_tac.
- by rewrite -> !(bi.pure_True (tc_val _ _)) by (by rewrite /nullval ?Hp).
- apply bi.and_proper; last done.
  apply bi.pure_iff.
  rewrite /nullval Hp; split; intros [??]; split; try intros ?; done.
*
simpl access_mode; cbv beta iota.
simpl type_is_volatile; cbv beta iota.
unfold Mptr; rewrite Hp.
if_tac.
- by rewrite -> !(bi.pure_True (tc_val _ _)) by (by rewrite /nullval ?Hp).
- apply bi.and_proper; last done.
  apply bi.pure_iff.
  rewrite /nullval Hp; split; intros [??]; split; try intros ?; done.
Qed.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v,
   Archi.ptr64 = false -> 
             mapsto sh (Tint I32 Signed noattr) v nullval ⊣⊢
             mapsto sh (Tpointer t noattr) v nullval.
Proof.
  intros.
  unfold mapsto, nullval; rewrite H; simpl.
  destruct v; auto.
  if_tac; f_equiv; f_equiv; rewrite /Mptr ?H /=; auto.
  - rewrite andb_false_r; iSplit; auto.
  - unfold tc_val', tc_val; simpl.
    rewrite andb_false_r /= H; tauto.
Qed.

Lemma repr_inj_unsigned:
  forall i j,
    0 <= i <= Int.max_unsigned ->
    0 <= j <= Int.max_unsigned ->
    Int.repr i = Int.repr j -> i=j.
Proof.
intros.
rewrite <- (Int.unsigned_repr i) by auto.
rewrite <- (Int.unsigned_repr j) by auto.
congruence.
Qed.

(* In case the Archi.big_endian is unknown (e.g. on ARM this is a parameter),
   the left hand side does not compute, which the right hand side does. *)

Lemma encode_nullval:
  encode_val (if Archi.ptr64 then Mint64 else Mint32) nullval
= repeat (Memdata.Byte Byte.zero) (if Archi.ptr64 then 8 else 4)%nat.
Proof.
  cbv delta [nullval Archi.ptr64 encode_val encode_int rev_if_be] beta iota.
  simple_if_tac; reflexivity.
Qed.

Lemma decode_encode_nullval :
  decode_val Mptr (encode_val (if Archi.ptr64 then Mint64 else Mint32) nullval) = nullval.
Proof.
  rewrite encode_nullval.
  cbv delta [Archi.ptr64 repeat decode_val decode_int proj_bytes rev_if_be rev Mptr Archi.ptr64] iota beta zeta.
  simple_if_tac; reflexivity.
Qed.

Lemma address_mapsto_zeros'_address_mapsto:
  forall sh ch b z,
   (align_chunk ch | z) ->
  (address_mapsto_zeros' (size_chunk ch) sh (b, z)
   ⊢ address_mapsto ch (decode_val ch (repeat (Byte Byte.zero) (Z.to_nat (size_chunk ch)))) sh (b, z)).
Proof.
  intros.
  iIntros "H".
  rewrite /address_mapsto_zeros' /address_mapsto.
  iExists (repeat (Byte Byte.zero) (size_chunk_nat ch)); iSplit.
  { rewrite repeat_length; auto. }
  rewrite (big_sepL_seq (repeat _ _)) repeat_length.
  iApply (big_sepL_mono with "H"); intros ?? [??]%lookup_seq.
  pose proof (@nth_In _ y (repeat (Byte Byte.zero) (size_chunk_nat ch)) inhabitant) as ->%repeat_spec; auto.
  rewrite repeat_length; simpl in *; subst; auto.
Qed.

Lemma decode_mptr_zero_nullval :
  decode_val Mptr (repeat (Byte Byte.zero) (size_chunk_nat Mptr)) = nullval.
Proof.
  cbv delta [repeat size_chunk_nat Z.to_nat size_chunk Mptr Archi.ptr64 Pos.to_nat Pos.iter_op Init.Nat.add] iota beta zeta.
  cbv delta [decode_val decode_int proj_bytes rev_if_be rev] iota beta zeta.
  simple_if_tac; reflexivity.
Qed.

Lemma address_mapsto_address_mapsto_zeros:
  forall sh b z,
  (align_chunk Mptr | z) ->
  address_mapsto_zeros' (size_chunk Mptr) sh (b,z)
  ⊢ res_predicates.address_mapsto Mptr nullval sh (b, z).
Proof.
  intros.
  by rewrite -decode_mptr_zero_nullval address_mapsto_zeros'_address_mapsto; done.
Qed.

Lemma mapsto_zeros_mapsto_nullval:
  forall sh b z t,
      readable_share sh ->
      (align_chunk Mptr | Ptrofs.unsigned z) -> 
      mapsto_zeros (size_chunk Mptr) sh (Vptr b z) ⊢
      ⌜0 <= Ptrofs.unsigned z /\ size_chunk Mptr + Ptrofs.unsigned z < Ptrofs.modulus⌝ ∧ mapsto sh (Tpointer t noattr) (Vptr b z) nullval.
Proof.
  intros.
  unfold mapsto_zeros, mapsto; simpl.
  rewrite -> if_true by auto.
  iIntros "[% H]"; iSplit; first done.
  iLeft; simpl; iSplit.
  { rewrite andb_false_r; auto. }
  by rewrite address_mapsto_zeros_eq address_mapsto_address_mapsto_zeros.
Qed.

Lemma address_mapsto_zeros'_split:
  forall a b sh p,
 0 <= a -> 0 <= b -> 
 address_mapsto_zeros' (a+b) sh p ⊣⊢
 address_mapsto_zeros' a sh p 
 ∗ address_mapsto_zeros' b sh (adr_add p a).
Proof.
  intros; rewrite /address_mapsto_zeros'.
  rewrite -> Z2Nat.inj_add, seq_app by auto.
  rewrite big_sepL_app Nat.add_0_l.
  rewrite -{2}(plus_0_r (Z.to_nat a)) -fmap_add_seq big_sepL_fmap.
  apply bi.sep_proper; first done; apply big_sepL_proper; intros.
  rewrite /adr_add /= Nat2Z.inj_add Z2Nat.id; auto.
  by rewrite Z.add_assoc.
Qed.

Lemma address_mapsto_zeros_split {sh b}: forall n n1 n2 z (N:(n=n1+n2)%nat),
      address_mapsto_zeros sh n (b,z) ⊢
      address_mapsto_zeros sh n1 (b,z) ∗
      address_mapsto_zeros sh n2 (b,Z.of_nat n1+z).
Proof.
  intros; subst; rewrite !address_mapsto_zeros_eq Nat2Z.inj_add address_mapsto_zeros'_split; try lia.
  by rewrite /adr_add /= Z.add_comm.
Qed.

Lemma mapsto_zeros_split sh a n1 n2 (N1: 0 <= n1) (N2: 0<=n2):
      mapsto_zeros (n1+n2) sh a ⊢ mapsto_zeros n1 sh a ∗ mapsto_zeros n2 sh (offset_val n1 a).
Proof.
  destruct a; simpl; try solve [rewrite bi.False_sep; trivial].
  rewrite -> Z2Nat.inj_add by lia.
  rewrite (address_mapsto_zeros_split (Z.to_nat n1 + Z.to_nat n2) (Z.to_nat n1) (Z.to_nat n2) _ (eq_refl _)).
  rewrite -> Z2Nat.id by auto.
  iIntros "(% & $ & ?)".
  rewrite Ptrofs.add_unsigned Ptrofs.unsigned_repr Ptrofs.unsigned_repr; try solve [split; unfold Ptrofs.max_unsigned; lia].
  rewrite {1}Z.add_comm; iFrame.
  iPureIntro; repeat (split; auto); lia.
Qed.

Fixpoint sepconN N (P: val -> mpred) sz (p: val): mpred :=
  match N with
  | O => emp
  | S n => (P p ∗ sepconN n P sz (offset_val sz p))
  end.

Lemma sepconN_big_sepL: forall N P sz p, isptr p ->
  sepconN N P sz p ⊣⊢ [∗ list] i ∈ seq 0 N, P (offset_val (sz * Z.of_nat i) p).
Proof.
  induction N; simpl; auto; intros.
  destruct p; try contradiction.
  rewrite -fmap_S_seq big_sepL_fmap IHN; last done.
  rewrite {3}/offset_val Z.mul_0_r Ptrofs.add_zero.
  iApply bi.sep_proper; first done.
  iApply big_sepL_proper; intros.
  replace (offset_val _ (offset_val _ _)) with (offset_val (sz * Z.of_nat (S y)) (Vptr b i)); first done.
  rewrite /offset_val /=.
  rewrite Nat2Z.inj_succ Z.mul_succ_r Ptrofs.add_assoc; do 2 f_equal.
  rewrite Ptrofs.add_unsigned.
  apply Ptrofs.eqm_samerepr.
  rewrite Z.add_comm; apply Ptrofs.eqm_add; apply Ptrofs.eqm_unsigned_repr.
Qed.

Lemma mapsto_zeros_mapsto_nullval_N {cenv sh b t}: forall N z,
       readable_share sh ->
       (align_chunk Mptr | Ptrofs.unsigned z) ->
       mapsto_zeros (Z.of_nat N * size_chunk Mptr) sh (Vptr b z)
       ⊢ ⌜0 <= Ptrofs.unsigned z /\
               Z.of_nat N * size_chunk Mptr + Ptrofs.unsigned z < Ptrofs.modulus⌝ ∧
           sepconN N (fun p => mapsto sh (Tpointer t noattr) p nullval)
                     (@sizeof cenv (Tpointer t noattr)) (Vptr b z).
Proof.
  induction N; intros; trivial. remember (size_chunk Mptr) as sz.
  replace (Z.of_nat (S N) * sz)%Z with (sz + Z.of_nat N * sz)%Z by lia.
  specialize (size_chunk_pos Mptr); intros. specialize (Z_of_nat_ge_O N); intros.
  rewrite mapsto_zeros_split; subst; try first [lia | apply Z.mul_nonneg_nonneg; lia].
  simpl sepconN; rewrite -> mapsto_zeros_mapsto_nullval by trivial.
  iIntros "[[% $] [%Hz ?]]".
  assert (Ptrofs.unsigned (Ptrofs.add z (Ptrofs.repr (size_chunk Mptr))) = Ptrofs.unsigned z + size_chunk Mptr) as Heq.
  { rewrite Ptrofs.add_unsigned !Ptrofs.unsigned_repr; unfold Ptrofs.max_unsigned; lia. }
  rewrite -(bi.True_and (address_mapsto_zeros _ _ _)) -bi.pure_True; last apply Hz.
  iSplit; [|iDestruct (IHN with "[$]") as "[_ $]"].
  - rewrite Heq in Hz; iPureIntro; repeat split; auto; lia.
  - rewrite Heq. by apply Z.divide_add_r, Z.divide_refl.
Qed.

Lemma address_mapsto_zeros'_nonlock_permission_bytes:
  forall n sh a,
  address_mapsto_zeros' n sh a ⊢ res_predicates.nonlock_permission_bytes sh a n.
Proof.
  intros; rewrite /address_mapsto_zeros' /nonlock_permission_bytes.
  apply big_sepL_mono; intros.
  iIntros "H".
  iDestruct (mapsto_valid with "H") as %[??].
  rewrite if_true; last done.
  iExists (VAL (Byte Byte.zero)); auto.
Qed.

Lemma mapsto_core_load: forall t ch sh v b o, access_mode t = By_value ch -> readable_share sh ->
  v <> Vundef ->
  mapsto sh t (Vptr b o) v ⊢ core_load ch (b, Ptrofs.unsigned o) v.
Proof.
  unfold mapsto.
  intros; rewrite H.
  iIntros "H".
  destruct (type_is_volatile t); try done.
  rewrite -> if_true by auto.
  iDestruct "H" as "[(% & H) | (% & % & H)]"; try done; iApply (mapsto_core_load with "H").
Qed.

End mpred.

#[export] Hint Resolve is_pointer_or_null_nullval : core.
#[export] Hint Resolve tc_val_pointer_nullval' : core.
#[export] Hint Resolve tc_val_pointer_nullval : core.
