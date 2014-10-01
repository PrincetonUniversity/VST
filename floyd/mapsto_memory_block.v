Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_field_lemmas.

Local Open Scope logic.

(******************************************

Lemmas of size_compatible and align_compatible

******************************************)

Lemma size_1_compatible: forall t, sizeof t = 1 -> forall p, size_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  destruct (Int.unsigned_range i).
  omega.
Qed.

Lemma size_0_compatible: forall t, sizeof t = 0 -> forall p, size_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  destruct (Int.unsigned_range i).
  omega.
Qed.

Lemma align_1_compatible: forall t, alignof t = 1 -> forall p, align_compatible t p.
Proof.
  intros.
  destruct p; simpl; auto.
  rewrite H.
  apply Z.divide_1_l.
Qed.

Lemma size_compatible_nested_field: forall t ids p,
  size_compatible t p ->
  size_compatible (nested_field_type2 t ids) (offset_val (Int.repr (nested_field_offset2 t ids)) p).
Proof.
  intros.
  destruct (isSome_dec (nested_field_rec t ids)).
  + destruct p; simpl; try tauto.
    repeat rewrite Int.Z_mod_modulus_eq.
    simpl in H.
    rewrite Zplus_mod_idemp_r.
    assert (0 < Int.modulus) by (cbv; reflexivity).
    assert (0 <= Int.unsigned i0 + nested_field_offset2 t ids) by (pose proof nested_field_offset2_in_range t ids i; pose proof Int.unsigned_range i0; omega).
    pose proof Zmod_le (Int.unsigned i0 + nested_field_offset2 t ids) (Int.modulus) H0 H1.
    pose proof nested_field_offset2_in_range t ids i.
    omega.
  + unfold nested_field_type2, nested_field_offset2.
    destruct (nested_field_rec t ids); [simpl in n; tauto|].
    destruct p; simpl; try tauto.
    repeat rewrite Int.Z_mod_modulus_eq.
    rewrite Zplus_0_r.
    assert (0 < Int.modulus) by (cbv; reflexivity).
    pose proof Int.unsigned_range i.
    assert (0 <= Int.unsigned i) by omega.
    pose proof Zmod_le (Int.unsigned i) (Int.modulus) H0 H2.
    omega.
Qed.

Lemma power_nat_one_divede_other: forall n m : nat,
  (two_power_nat n | two_power_nat m) \/ (two_power_nat m | two_power_nat n).
Proof.
  intros.
  pose proof Zle_0_nat n.
  pose proof Zle_0_nat m.
  rewrite !two_power_nat_two_p.
  destruct (zle (Z.of_nat n) (Z.of_nat m)).
  + left.
    exists (two_p (Z.of_nat m - Z.of_nat n)).
    rewrite <- two_p_is_exp by omega.
    f_equal.
    omega.
  + right.
    exists (two_p (Z.of_nat n - Z.of_nat m)).
    rewrite <- two_p_is_exp by omega.
    f_equal.
    omega.
Qed.

Lemma multiple_divide_mod: forall a b c, b > 0 -> ((a | b) \/ (b | a)) -> (a | (c * a mod b)).
Proof.
  intros.
  destruct H0.
  + apply Z.divide_add_cancel_r with (b * (c * a / b))%Z.
    apply Z.divide_mul_l; auto.
    rewrite <- Z_div_mod_eq; auto.
    apply Z.divide_mul_r, Z.divide_refl.
  + destruct H0.
    subst.
    rewrite Z.mul_assoc, Z_mod_mult.
    apply Z.divide_0_r.
Qed.

Lemma align_compatible_nested_field: forall t ids p,
  legal_alignas_type t = true ->
  align_compatible t p ->
  align_compatible (nested_field_type2 t ids) (offset_val (Int.repr (nested_field_offset2 t ids)) p).
Proof.
  intros.
  destruct (isSome_dec (nested_field_rec t ids)).
  + destruct p; simpl in *; try tauto.
    repeat rewrite Int.Z_mod_modulus_eq.
    rewrite Zplus_mod_idemp_r.
    assert (alignof (nested_field_type2 t ids) | Int.unsigned i0 + nested_field_offset2 t ids).
    - apply Z.divide_add_r; auto.
      eapply Z.divide_trans; [| eauto].
      apply alignof_nested_field_type2_divide; auto.
      apply nested_field_offset2_type2_divide; auto.
    - unfold Int.modulus.
      destruct (alignof_two_p (nested_field_type2 t ids)).
      rewrite H2 in *.
      destruct H1.
      rewrite H1.
      rewrite !two_power_nat_two_p in *.
      apply multiple_divide_mod.
      * apply two_p_gt_ZERO, Zle_0_nat.
      * rewrite <- !two_power_nat_two_p in *. apply power_nat_one_divede_other.
  + unfold nested_field_type2, nested_field_offset2.
    destruct (nested_field_rec t ids); [simpl in n; tauto|].
    destruct p; simpl; try tauto.
Transparent alignof.
    simpl alignof.
Opaque alignof.
    apply Z.divide_1_l.
Qed.

(******************************************

Basic lemmas about local_facts, isptr, offset_zero

******************************************)

Lemma local_facts_isptr: forall P (p: val), P p |-- !! isptr p -> P p = !! (isptr p) && P p.
Proof.
  intros.
  apply pred_ext.
  + apply andp_right.
    exact H.
    cancel.
  + apply andp_left2.
    cancel.
Qed.

Lemma local_facts_offset_zero: forall P, (forall p, P p |-- !! isptr p) -> (forall p, P p = P (offset_val Int.zero p)).
Proof.
  intros.
  pose proof (H p).
  pose proof (H Vundef).
  destruct p; simpl in *; apply pred_ext; normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
  + eapply derives_trans. exact H0. normalize.
  + eapply derives_trans. exact H1. normalize.
Qed.

(******************************************

Lemmas about mapsto and mapsto_.

******************************************)

Lemma mapsto_mapsto_: forall sh t v v', mapsto sh t v v' |-- mapsto_ sh t v.
Proof. unfold mapsto_; intros.
  normalize.
  unfold mapsto.
  destruct (access_mode t); auto.
  destruct (type_is_volatile t); try apply FF_left.
  destruct v; auto.
  apply orp_left.
  apply orp_right2.
  apply andp_left2.
  apply andp_right. apply prop_right; auto.
  apply exp_right with v'; auto.
  normalize.
  apply orp_right2. apply exp_right with v2'.
  normalize.
Qed.
Hint Resolve mapsto_mapsto_ : cancel.

Lemma mapsto_local_facts:
  forall sh t v1 v2,  mapsto sh t v1 v2 |-- !! (isptr v1).
  (* could make this slightly stronger by adding the fact
     (tc_val t v2 \/ v2=Vundef)  *)
Proof.
intros; unfold mapsto.
destruct (access_mode t); try apply FF_left.
destruct (type_is_volatile t); try apply FF_left.
destruct v1; try apply FF_left.
apply prop_right; split; auto; apply I.
Qed.

Lemma mapsto__local_facts:
  forall sh t v1, mapsto_ sh t v1 |-- !! (isptr v1).
Proof.
intros; apply mapsto_local_facts.
Qed.
Hint Resolve mapsto_local_facts mapsto__local_facts : saturate_local.

Lemma mapsto_offset_zero:
  forall sh t v1 v2, mapsto sh t v1 v2 = mapsto sh t (offset_val Int.zero v1) v2.
Proof.
  intros.
  change (mapsto sh t (offset_val Int.zero v1) v2) with ((fun v0 => mapsto sh t v0 v2) (offset_val Int.zero v1)).
  rewrite <- local_facts_offset_zero.
  reflexivity.
  intros.
  apply mapsto_local_facts.  
Qed.

Lemma mapsto__offset_zero:
  forall sh t v1, mapsto_ sh t v1 = mapsto_ sh t (offset_val Int.zero v1).
Proof.
  unfold mapsto_.
  intros.
  apply mapsto_offset_zero.
Qed.

Lemma mapsto_isptr: forall sh t v1 v2, mapsto sh t v1 v2 = !! (isptr v1) && mapsto sh t v1 v2.
Proof.
  intros.
  change (mapsto sh t v1 v2) with ((fun v1 => mapsto sh t v1 v2) v1).
  rewrite <- local_facts_isptr.
  reflexivity.
  apply mapsto_local_facts.
Qed.

Lemma mapsto__isptr: forall sh t v1, mapsto_ sh t v1 = !! (isptr v1) && mapsto_ sh t v1.
Proof.
  intros.
  unfold mapsto_. apply mapsto_isptr.
Qed.

(******************************************

Lemmas about memory_block

******************************************)

Lemma memory_block_zero: forall sh b z, memory_block sh (Int.repr 0) (Vptr b z) = emp.
Proof.
  intros. unfold memory_block.
  change (Int.repr 0) with Int.zero.
  rewrite Int.unsigned_zero.
  change (nat_of_Z 0) with (0%nat).
  unfold memory_block'.
  pose proof Int.unsigned_range z.
  assert (Int.unsigned z <= Int.modulus) by omega.
  apply pred_ext; normalize.
Qed.
Hint Rewrite memory_block_zero: norm.

Lemma memory_block_local_facts: forall sh n p, memory_block sh n p |-- !! (isptr p).
Proof.
  intros.
  destruct p; simpl; normalize.
Qed.
Hint Resolve memory_block_local_facts : saturate_local.

Lemma memory_block_offset_zero:
  forall sh n v, memory_block sh n v = memory_block sh n (offset_val Int.zero v).
Proof.
  intros.
  rewrite <- local_facts_offset_zero.
  reflexivity.
  apply memory_block_local_facts.
Qed.

Lemma memory_block_isptr: forall sh n p, memory_block sh n p = !!(isptr p) && memory_block sh n p.
Proof.
  intros.
  rewrite <- local_facts_isptr.
  reflexivity.
  apply memory_block_local_facts.
Qed.

(******************************************

To prove memory_block_mapsto_

******************************************)

(*** This part are totally written on a lower leverl. So, It might be better to 
move to somewhere else ***)

Lemma access_mode_by_value: forall t, type_is_by_value t -> exists ch, access_mode t = By_value ch.
Proof.
  intros.
  assert (forall ch', exists ch, By_value ch' = By_value ch).
    intros. exists ch'. reflexivity.
  destruct t; inversion H; simpl.
  - destruct i, s; apply H0.
  - apply H0.
  - destruct f; apply H0.
  - apply H0.
Qed.

Lemma repr_unsigned: forall i, Int.repr (Int.unsigned i) = i.
Proof.
  intros.
  apply Int.eqm_repr_eq.
  apply Int.eqm_refl.
Qed.

Lemma FF_orp: forall {A: Type} `{NatDed A} (P: A), FF || P = P.
Proof.
  intros.
  apply pred_ext.
  + apply orp_left.
    apply FF_left.
    apply derives_refl.
  + apply orp_right2.
    apply derives_refl.
Qed.

Lemma mapsto__exp_address_mapsto:
  forall sh t b i_ofs ch,
   access_mode t = By_value ch ->
   type_is_volatile t = false ->
   mapsto_ sh t (Vptr b i_ofs) = EX  v2' : val,
             address_mapsto ch v2' (Share.unrel Share.Lsh sh)
               (Share.unrel Share.Rsh sh) (b, (Int.unsigned i_ofs)).
Proof.
  intros.
  unfold mapsto_, mapsto.
  rewrite H.
  assert (!!(tc_val t Vundef) = @FF mpred Nveric)
    by (destruct t as [ | | | [ | ] |  | | | | | ]; reflexivity).
  rewrite H1.
  rewrite FF_andp, FF_orp.
  assert (!!(Vundef = Vundef) = @TT mpred Nveric) by (apply pred_ext; normalize).
  rewrite H2.
  rewrite TT_andp.
  rewrite H0.
  reflexivity.
Qed.

Fixpoint list_address_mapsto ch vs rsh sh b ofs :=
  match vs with
  | nil => emp
  | v :: vs' => address_mapsto ch v rsh sh (b, Int.unsigned (Int.repr ofs)) * list_address_mapsto ch vs' rsh sh b (ofs + 1)
  end.

Lemma memory_block'_list_address_mapsto: forall sh n b ofs, memory_block' sh n b ofs = EX vs: list val, (!! (length vs = n)) && list_address_mapsto Mint8unsigned vs (Share.unrel Share.Lsh sh) (Share.unrel Share.Rsh sh) b ofs.
Proof.
  intros.
  apply pred_ext; revert ofs; induction n; intros.
  + apply (exp_right nil).
    simpl.
    normalize.
  + simpl.
    erewrite mapsto__exp_address_mapsto; [|reflexivity|simpl; reflexivity].
    eapply derives_trans; [apply sepcon_derives; [apply derives_refl| exact (IHn (ofs + 1))]|].
    normalize.
    apply (exp_right (x :: v2')).
    simpl.
    normalize.
  + normalize. 
    destruct vs; simpl; [normalize | inversion H].
  + normalize.
    destruct vs; simpl; inversion H.
    erewrite mapsto__exp_address_mapsto; [|reflexivity|simpl; reflexivity].
    apply sepcon_derives. 
    - apply (exp_right v).
      normalize.
    - rewrite H1. eapply derives_trans; [| exact (IHn (ofs + 1))].
      apply (exp_right vs).
      normalize.
Qed.

(*
(* not used here, but could be moved elsewhere *)

Lemma allp_forall: forall A P Q (x:A), (forall x:A, (P x = Q)) -> (allp P = Q).
Proof.
  intros.
  apply pred_ext.
  + apply (allp_left _ x).
    rewrite H.
    apply derives_refl.
  + apply allp_right.
    intros.
    rewrite H.
    apply derives_refl.
Qed.

Lemma allp_andp: forall P Q, allp (P && Q) = allp P && allp Q.
Proof.
  intros.
  apply pred_ext.
  + apply andp_right; apply allp_derives; intros;
    simpl; [apply andp_left1|apply andp_left2]; apply derives_refl.
  + apply allp_right; intros.
    simpl; apply andp_right; [apply andp_left1|apply andp_left2];
    apply (allp_left _ v); apply derives_refl.
Qed.
*)
Lemma address_mapsto_VALspec_range'_aux: forall n l P, n >= 0 -> (forall l0, adr_range l n l0 -> exists v, P l0 v) -> (exists vs, length vs = nat_of_Z n /\ (forall l0, adr_range l n l0 -> P l0 (nth (nat_of_Z (snd l0 - snd l)) vs Memdata.Undef))).
Proof.
  intros.
  remember (nat_of_Z n) as m.
  assert (Z_of_nat m = n) by (subst m; apply (nat_of_Z_eq _ H)); clear Heqm; subst n.
  clear H.
  revert l H0; induction m; intros.
  + exists nil; split; [reflexivity |intros].
    unfold adr_range in H; destruct l, l0. destruct H as [? [? ?]]; subst. 
    change (Z.of_nat 0) with 0 in H2. omega.
  + assert (forall l0 : address, adr_range (fst l, snd l + 1) (Z.of_nat m) l0 ->
      exists v : Memdata.memval, P l0 v).
      intros.
      assert (adr_range l (Z.of_nat (S m)) l0).
        unfold adr_range in *.
        destruct l, l0.
        simpl in H.
        destruct H as [? [? ?]].
        subst; split; [reflexivity| split]. omega.
        rewrite Nat2Z.inj_succ; rewrite <- Z.add_1_l. omega.
      exact (H0 l0 H1).
    destruct (IHm (fst l, snd l + 1) H) as [v_tl ?].
    destruct H1.
    destruct (H0 l) as [v_hd ?].
      unfold adr_range; destruct l.
      split; [reflexivity|split; [|rewrite Nat2Z.inj_succ; rewrite <- Z.add_1_l]; omega].
    exists (v_hd :: v_tl).
    split; [simpl; rewrite H1; reflexivity|].
    intros.
    destruct (adr_range_dec l 1 l0).
    - unfold adr_range in a; destruct l0, l; destruct a as [? [? ?]].
      assert (z = z0) by omega; subst.
      rewrite <- Zminus_diag_reverse.
      simpl. exact H3.
    - unfold adr_range in *; destruct l, l0; simpl.
      destruct H4 as [? [? ?]].
      destruct (zlt z0 (z + 1)); [pose proof n (conj H4 (conj H5 l)); inversion H7|clear n].
      rewrite Nat2Z.inj_succ in H6; rewrite <- Z.add_1_l in H6.
      assert (fst (b, z) = b0 /\
        snd (b, z) + 1 <= z0 < z + 1 + Z.of_nat m).
        split; [exact H4| split;[simpl|]; omega].
      simpl in *.
      pose proof H2 (b0, z0) H7.
      simpl in H8.
      replace (nat_of_Z (z0 - z)) with (S (nat_of_Z (z0 - (z + 1)))); [exact H8|].
      replace (z0 - z) with ((z0 - (z + 1)) + 1) by omega.
      rewrite nat_of_Z_plus; [|omega|omega].
      change (nat_of_Z 1) with 1%nat.
      omega.
Qed.

Lemma address_mapsto_VALspec_range':
  forall (ch : memory_chunk) (rsh sh : Share.t)
    (l : compcert_rmaps.RML.R.AV.address),
    (Memdata.align_chunk ch | snd l) ->
    exp (fun v => res_predicates.address_mapsto ch v rsh sh l) = 
    (res_predicates.VALspec_range (Memdata.size_chunk ch) rsh sh l).
Proof.
  intros.
  apply pred_ext.
  + normalize.
    apply res_predicates.address_mapsto_VALspec_range.
  + unfold res_predicates.VALspec_range.
    change derives with (@predicates_hered.derives compcert_rmaps.RML.R.rmap compcert_rmaps.R.ag_rmap).
    change (@predicates_hered.pred compcert_rmaps.RML.R.rmap compcert_rmaps.R.ag_rmap) with mpred.
    change (@exp mpred Nveric) with (@predicates_hered.exp compcert_rmaps.RML.R.rmap compcert_rmaps.R.ag_rmap).
    unfold predicates_hered.derives, predicates_hered.allp, res_predicates.jam.
    simpl in *.
    intros.
    assert (forall b : address, adr_range l (Memdata.size_chunk ch) b -> exists b0,
      exists (p : sepalg.nonunit sh), @eq compcert_rmaps.RML.R.resource
                  (compcert_rmaps.RML.R.resource_at a b)
                  (compcert_rmaps.RML.R.YES rsh
                     (@psepalg.mk_lifted Share.t Share.Join_ba sh p)
                     (compcert_rmaps.VAL b0)
                     (compcert_rmaps.RML.R.SomeP
                        (@cons Type sepalg_generators.Void (@nil Type))
                        (@base.compose (prod sepalg_generators.Void unit)
                           (@predicates_hered.pred compcert_rmaps.RML.R.rmap
                              compcert_rmaps.RML.R.ag_rmap)
                           (@predicates_hered.pred compcert_rmaps.RML.R.rmap
                              compcert_rmaps.RML.R.ag_rmap)
                           (compcert_rmaps.RML.R.approx
                              (@ageable.level compcert_rmaps.RML.R.rmap
                                 compcert_rmaps.R.ag_rmap a))
                           (fun _ : prod sepalg_generators.Void unit =>
                            @predicates_hered.FF compcert_rmaps.RML.R.rmap
                              compcert_rmaps.RML.R.ag_rmap))))).
      intros.
      pose proof H0 b.
      destruct (adr_range_dec l (Memdata.size_chunk ch) b); [exact H2|congruence].
    apply address_mapsto_VALspec_range'_aux in H1.
    destruct H1 as [vs [? ?]].
    exists (Memdata.decode_val ch vs).
    exists vs.
    repeat split.
    - unfold Memdata.size_chunk_nat.
      exact H1.
    - exact H.
    - intros.
      pose proof H0 b; clear H0.
      destruct (adr_range_dec l (Memdata.size_chunk ch) b);
      [apply H2; exact a0 | exact H3].
    - pose proof size_chunk_pos ch. omega.
Qed.

Lemma allp_jam_range_basic: forall b ofs P,
  allp (res_predicates.jam (adr_range_dec (b, ofs) 0) P res_predicates.noat) = emp.
Proof.
  intros.
  assert ((res_predicates.jam (adr_range_dec (b, ofs) 0) P res_predicates.noat) =
    res_predicates.noat).
    extensionality.  
    apply res_predicates.jam_false.
    unfold not.
    unfold adr_range; intros.
    destruct x.
    destruct H.
    omega.
  rewrite H.
  change emp with predicates_sl.emp.
  change allp with (@predicates_hered.allp compcert_rmaps.RML.R.rmap compcert_rmaps.R.ag_rmap address).
  apply res_predicates.allp_noat_emp.
Qed.

Lemma address_mapsto_list_address_mapsto_Mint8unsigned:
  forall ch rsh sh b ofs, (Memdata.align_chunk ch | ofs) -> 
  (Memdata.size_chunk ch + ofs <= Int.modulus) ->
  ofs >= 0 ->
  EX v:val, address_mapsto ch v rsh sh (b, ofs) = 
  EX vs:list val, !! (length vs = Memdata.size_chunk_nat ch) && list_address_mapsto Mint8unsigned vs rsh sh b ofs.
Proof.
  intros. rename H0 into H99. rename H1 into H98.
  rewrite address_mapsto_VALspec_range'; [|simpl; exact H].
  rewrite Memdata.size_chunk_conv in *.
  clear H.
  forget (Memdata.size_chunk_nat ch) as n.
  revert ofs H99 H98; induction n; intros.
  + intros.
    change (Z.of_nat 0) with 0.
    rewrite res_predicates.VALspec_range_0.
    apply pred_ext.
    - apply (exp_right nil).
      normalize.
    - normalize.
      destruct vs; inversion H.
      simpl.
      apply derives_refl.
  + erewrite res_predicates.VALspec_range_split2; [|
      rewrite Nat2Z.inj_succ; rewrite <- Z.add_1_l; reflexivity |
      omega |
      apply seplog.Z_of_nat_ge_O].
    change 1 with (Memdata.size_chunk Mint8unsigned) at 1.
    rewrite <- address_mapsto_VALspec_range' at 1; [|simpl; apply Z.divide_1_l].
    rewrite Nat2Z.inj_succ in H99; rewrite <- Z.add_1_l in H99.
    rewrite IHn; [| omega|omega].
    change predicates_sl.sepcon with sepcon.
    assert (Int.Z_mod_modulus ofs = ofs).
      rewrite Int.Z_mod_modulus_eq.
      rewrite Zmod_small; [reflexivity|split; try omega].
    apply pred_ext.
    - normalize.
      apply (exp_right (x :: v)).
      normalize.
      simpl.
      rewrite H; apply derives_refl.
    - normalize.
      destruct vs; inversion H0.
      apply (exp_right vs).
      normalize.
      apply (exp_right v).
      simpl.
      rewrite H; apply derives_refl.
Qed.

Lemma align_chunk_alignof: forall t ch, access_mode t = By_value ch -> legal_alignas_type t = true -> alignof t = Memdata.align_chunk ch.
Proof.
Transparent alignof.
  intros.
  destruct t; inversion H.
  - unfold legal_alignas_type in H0.
    simpl in H0.
    destruct i, s; inversion H2; simpl;
    destruct (attr_alignas a); try inversion H0; reflexivity.
  - unfold legal_alignas_type in H0.
    simpl in H0.
    destruct s; inversion H2; simpl;
    destruct (attr_alignas a); try inversion H0; admit. (* Tlong uncompatible problem *)
  - unfold legal_alignas_type in H0.
    simpl in H0.
    destruct f; inversion H2; simpl;
    destruct (attr_alignas a); try inversion H0; reflexivity.
  - unfold legal_alignas_type in H0.
    simpl in H0.
    inversion H2; simpl;
    destruct (attr_alignas a); try inversion H0; reflexivity.
Opaque alignof.
Qed.

Lemma size_chunk_sizeof: forall t ch, access_mode t = By_value ch -> sizeof t = Memdata.size_chunk ch.
Proof.
  intros.
  destruct t; inversion H.
  - destruct i, s; inversion H1; reflexivity.
  - destruct s; inversion H1; reflexivity.
  - destruct f; inversion H1; reflexivity.
  - inversion H1; reflexivity.
Qed.

Lemma memory_block_mapsto__aux:
  forall n sh t b i_ofs,
   type_is_by_value t ->
   type_is_volatile t = false ->
   legal_alignas_type t = true ->
   (alignof t | Int.unsigned i_ofs) ->
   Int.unsigned n = sizeof t ->
   sizeof t + Int.unsigned i_ofs <= Int.modulus ->
   memory_block sh n (Vptr b i_ofs) = mapsto_ sh t (Vptr b i_ofs).
Proof.
  intros.
  unfold memory_block.
  rewrite memory_block'_list_address_mapsto.
  destruct (access_mode_by_value t H) as [ch ?].
  erewrite mapsto__exp_address_mapsto; [|exact H5|exact H0].
  rewrite address_mapsto_list_address_mapsto_Mint8unsigned; 
    [| erewrite align_chunk_alignof in H2; [exact H2| exact H5| exact H1] 
     | erewrite <- size_chunk_sizeof; [exact H4|exact H5]
     | destruct (Int.unsigned_range i_ofs); omega
    ].
  unfold Memdata.size_chunk_nat.
  erewrite size_chunk_sizeof in H3; [| exact H5].
  rewrite H3.
  assert (Int.unsigned i_ofs + Memdata.size_chunk ch <= Int.modulus) by 
    (erewrite <- size_chunk_sizeof; [|exact H5]; omega).
  apply pred_ext; normalize; apply (exp_right vs); normalize.
Qed.

Lemma memory_block_mapsto_:
  forall n sh t p, 
   type_is_by_value t ->
   type_is_volatile t = false ->
   legal_alignas_type t = true ->
   Int.unsigned n = sizeof t ->
   size_compatible t p ->
   align_compatible t p ->
   memory_block sh n p = mapsto_ sh t p.
Proof.
  intros.
  destruct p.
  + unfold mapsto_, mapsto; destruct (access_mode t), (type_is_volatile t); reflexivity.
  + unfold mapsto_, mapsto; destruct (access_mode t), (type_is_volatile t); reflexivity.
  + unfold mapsto_, mapsto; destruct (access_mode t), (type_is_volatile t); reflexivity.
  + unfold mapsto_, mapsto; destruct (access_mode t), (type_is_volatile t); reflexivity.
  + unfold mapsto_, mapsto; destruct (access_mode t), (type_is_volatile t); reflexivity.
  + apply memory_block_mapsto__aux; try assumption.
    simpl in H3.
    omega.
Qed.

Lemma memory_block_size_compatible:
  forall sh t p,
  sizeof t < Int.modulus ->
  memory_block sh (Int.repr (sizeof t)) p = 
  !! (size_compatible t p) && memory_block sh (Int.repr (sizeof t)) p.
Proof.
  intros.
  unfold memory_block, size_compatible.
  replace (Int.unsigned (Int.repr (sizeof t))) with (sizeof t).
  apply pred_ext; destruct p; normalize.
  pose proof sizeof_pos t. 
  rewrite Int.unsigned_repr; [reflexivity|].
  unfold Int.max_unsigned.
  omega.
Qed.

Lemma mapsto_align_compatible:
  forall sh t p v, legal_alignas_type t = true ->
  mapsto sh t p v = !!( align_compatible t p) && mapsto sh t p v.
Proof.
  intros.
  unfold mapsto, align_compatible.
  destruct (access_mode t) eqn:?, (type_is_volatile t), p;
  apply pred_ext; normalize.
  unfold address_mapsto, res_predicates.address_mapsto.
  apply andp_right; [|cancel].
  erewrite align_chunk_alignof by eassumption.
  apply orp_left.
  + change (@predicates_hered.exp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap (list Memdata.memval)) with (@exp mpred _ (list Memdata.memval)).
    normalize.
    change (@predicates_hered.andp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@andp mpred _ ).
    change (@predicates_hered.prop compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@prop mpred _ ).
    normalize.
  + change (@predicates_hered.exp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap (list Memdata.memval)) with (@exp mpred _ (list Memdata.memval)).
    normalize.
    change (@predicates_hered.andp compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@andp mpred _ ).
    change (@predicates_hered.prop compcert_rmaps.RML.R.rmap
        compcert_rmaps.R.ag_rmap) with (@prop mpred _ ).
    normalize.
Qed.

Lemma mapsto_by_value: forall sh t p v, mapsto sh t p v = !! (type_is_by_value t) && mapsto sh t p v.
Proof.
  intros.
  apply pred_ext; normalize.
  apply andp_right; [|cancel].
  unfold mapsto.
  destruct t; simpl; normalize; try (apply prop_right; auto).
Qed.

Lemma mapsto_size_compatible_aux: forall t, type_is_by_value t -> legal_alignas_type t = true -> alignof t < Int.modulus.
Proof.
  unfold legal_alignas_type.
  intros. 
  destruct t; inversion H.
Transparent alignof.
  + destruct i, s; unfold alignof; simpl in *; destruct (attr_alignas a); try inversion H0; try reflexivity.
  + destruct s; unfold alignof; simpl in *; destruct (attr_alignas a); try inversion H0; try reflexivity.
  + destruct f; unfold alignof; simpl in *; destruct (attr_alignas a); try inversion H0; try reflexivity.
  + unfold alignof; simpl in *; destruct (attr_alignas a); try inversion H0; try reflexivity.
Opaque alignof.
Qed.

Lemma mapsto_size_compatible:
  forall sh t p v, legal_alignas_type t = true ->
  sizeof t = alignof t ->
  mapsto sh t p v = !!(size_compatible t p) && mapsto sh t p v.
Proof.
  intros.
  apply pred_ext; normalize.
  apply andp_right; [|cancel].
  rewrite mapsto_align_compatible by assumption.
  unfold size_compatible, align_compatible.
  pose proof alignof_pos t.
  rewrite mapsto_by_value.
  normalize; apply prop_right.
  destruct p; auto.
  destruct (alignof_two_p t).
  rewrite H0.
  pose proof mapsto_size_compatible_aux t H3 H.
  rewrite H4 in *.
  clear t H H0 H3 H4.
  pose proof Int.unsigned_range i.
  unfold Int.modulus in *.
  destruct H2 as [K ?].
  rewrite H0 in *; clear H0.
  rewrite !two_power_nat_two_p in *.
  pose proof Zle_0_nat x.
  pose proof Zle_0_nat Int.wordsize.
  forget (Z.of_nat x) as X.
  forget (Z.of_nat Int.wordsize) as Y.
  destruct (zle Y X).
  + pose proof two_p_monotone Y X (conj H2 l).
    omega.
  + replace Y with ((Y-X) + X) in H by omega.
    rewrite two_p_is_exp in H by omega.
    destruct H.
    apply Z.mul_lt_mono_pos_r in H3; [|omega].
    replace Y with ((Y-X) + X) by omega.
    rewrite two_p_is_exp by omega.
    rewrite Zmult_succ_l_reverse.
    apply Z.mul_le_mono_pos_r; omega.
Qed.

Global Opaque memory_block.

(******************************************

Other lemmas

******************************************)

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh tuint = mapsto sh tint.
Proof.
intros.
extensionality v1 v2.
reflexivity.
Qed.

Lemma mapsto_mapsto__int32:
  forall sh p v s1 s2,
  mapsto sh (Tint I32 s1 noattr) p v |-- mapsto_ sh (Tint I32 s2 noattr) p.
Proof.
intros.
eapply derives_trans; [ apply mapsto_mapsto_ | ].
destruct s1,s2; fold tuint; fold tint; 
  repeat rewrite mapsto_tuint_tint; auto.
Qed.

Hint Extern 2 (mapsto _ _ _ _ |-- mapsto_ _ _ _) =>
   (apply mapsto_mapsto__int32)  : cancel.

Lemma mapsto_mapsto_int32:
  forall sh p v s1 s2,
  mapsto sh (Tint I32 s1 noattr) p v |-- mapsto sh (Tint I32 s2 noattr) p v.
Proof.
intros.
destruct s1,s2; fold tuint; fold tint; 
  repeat rewrite mapsto_tuint_tint; auto.
Qed.

Hint Extern 2 (mapsto _ _ _ _ |-- mapsto _ _ _ _) =>
   (apply mapsto_mapsto_int32)  : cancel.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v, 
             mapsto sh tint v nullval = 
             mapsto sh (tptr t) v nullval.
Proof.
intros.
unfold mapsto.
simpl.
destruct v; auto. f_equal; auto.
f_equal. f_equal.
apply prop_ext; split; intro; hnf in *|-*; auto.
Qed.

Lemma offset_val_force_ptr:
  offset_val Int.zero = force_ptr.
Proof. extensionality v. destruct v; try reflexivity.
simpl. rewrite Int.add_zero; auto.
Qed.

Hint Rewrite <- offset_val_force_ptr : norm.
Hint Extern 0 (legal_alignas_type _ = true) => reflexivity : cancel.

Lemma mapsto_force_ptr: forall sh t v v', 
  mapsto sh t (force_ptr v) v' = mapsto sh t v v'.
Proof.
intros.
destruct v; simpl; auto.
Qed.

Hint Rewrite mapsto_force_ptr: norm.