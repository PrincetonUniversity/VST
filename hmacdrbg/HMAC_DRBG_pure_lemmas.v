Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import VST.floyd.functional_base.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.

Require Import sha.general_lemmas.
Require Import sha.hmac_pure_lemmas.

Lemma HMAC_DRBG_generate_helper_Z_any_prop_fst:
  forall (P: list byte -> Prop) HMAC key v z,
    0 <= z ->
    P v ->
    (forall x y, P (HMAC x y)) ->
    P (fst (HMAC_DRBG_generate_helper_Z HMAC key v z)).
Proof.
  intros P HMAC key v z Hz Hv H.
  remember (z/32) as n.
  rewrite <- (Z2Nat.id n) in Heqn by (subst; apply (Z_div_pos z 32); omega).
  generalize dependent z.
  induction (Z.to_nat n); intros.
  {
    rewrite (Z_div_mod_eq z 32); try omega.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    rewrite <- Heqn.
    change (Z.of_nat 0) with 0.
    change (32 * 0 + z mod 32) with (z mod 32).
    change (Z.of_nat 32) with 32.
    remember (0 >=? z mod 32) as zero_geb_z; destruct zero_geb_z.
    auto.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    remember (0 >=? z mod 32 - 32) as zero_geb_z_minus_32; destruct zero_geb_z_minus_32.
    apply H.
    {
      rewrite Z.geb_leb in Heqzero_geb_z_minus_32.
      symmetry in Heqzero_geb_z_minus_32; apply Z.leb_gt in Heqzero_geb_z_minus_32.
      pose proof (Z_mod_lt z 32); omega.
    }
  }
  {
    rewrite (Z_div_mod_eq z 32); try omega.
    rewrite <- Heqn.
    assert (Hn: 32 * Z.of_nat (S n0) + z mod 32 = 32 * Z.of_nat n0 + z mod 32 + 32).
    {
      rewrite Nat2Z.inj_succ.
      rewrite <- Zmult_succ_r_reverse.
      omega.
    }
    rewrite Hn.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    destruct (0 >=? 32 * Z.of_nat n0 + z mod 32 + 32); auto.
    change (Z.of_nat 32) with 32.
    replace (32 * Z.of_nat n0 + z mod 32 + 32 - 32) with (32 * Z.of_nat n0 + z mod 32) by omega.
    remember (HMAC_DRBG_generate_helper_Z HMAC key v
               (32 * Z.of_nat n0 + z mod 32)) as result; destruct result.
    simpl.
    apply H.
  }
Qed.

Lemma HMAC_DRBG_generate_helper_Z_incremental_fst:
  forall HMAC key v z v',
    0 <= z ->
    v' = fst (HMAC_DRBG_generate_helper_Z HMAC key v z) ->
    HMAC v' key = fst (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32)).
Proof.
  intros HMAC key v z v' Hz H.
  remember (z/32) as n.
  rewrite <- (Z2Nat.id n) in Heqn by (subst; apply (Z_div_pos z 32); omega).
  assert (Hf: 0 >=? z + 32 = false).
  {
    assert (0 < z + 32) by omega.
    rewrite Z.geb_leb.
    apply Z.leb_gt; omega.
  }
  rewrite HMAC_DRBG_generate_helper_Z_equation.
  rewrite Hf.
  remember (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32 - Z.of_nat 32)) as result; destruct result.
  simpl.
  replace l with (fst (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32 - Z.of_nat 32))) by (rewrite <- Heqresult; auto).
  change (Z.of_nat 32) with 32.
  replace (z + 32 - 32) with z by omega.
  rewrite H.
  reflexivity.
Qed.

Lemma HMAC_DRBG_generate_helper_Z_incremental_snd:
  forall HMAC key v z v',
    0 <= z ->
    v' = fst (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32)) ->
    snd (HMAC_DRBG_generate_helper_Z HMAC key v z) ++ v' = snd (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32)).
Proof.
  intros HMAC key v z v' Hz H.
  remember (z/32) as n.
  rewrite <- (Z2Nat.id n) in Heqn by (subst; apply (Z_div_pos z 32); omega).
  assert (Hf: 0 >=? z + 32 = false).
  {
    assert (0 < z + 32) by omega.
    rewrite Z.geb_leb.
    apply Z.leb_gt; omega.
  }
  remember (HMAC_DRBG_generate_helper_Z HMAC key v z) as saved;
    rewrite HMAC_DRBG_generate_helper_Z_equation; subst saved.
  rewrite Hf.
  remember (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32 - Z.of_nat 32)) as result; destruct result.
  simpl.
  replace l with (fst (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32 - Z.of_nat 32))) by (rewrite <- Heqresult; auto).
  replace l0 with (snd (HMAC_DRBG_generate_helper_Z HMAC key v (z + 32 - Z.of_nat 32))) by (rewrite <- Heqresult; auto).
  change (Z.of_nat 32) with 32.
  replace (z + 32 - 32) with z by omega.
  rewrite H.
  erewrite <- HMAC_DRBG_generate_helper_Z_incremental_fst; eauto.
Qed.

Lemma HMAC_DRBG_generate_helper_Z_Zlength_fst:
  forall HMAC key v z,
    0 <= z ->
    Zlength v = 32 ->
    (forall x y, Zlength (HMAC x y) = 32) ->
    Zlength (fst (HMAC_DRBG_generate_helper_Z HMAC key v z)) = 32.
Proof.
  apply HMAC_DRBG_generate_helper_Z_any_prop_fst.
Qed.

Lemma HMAC_DRBG_generate_helper_Z_Zlength_snd:
  forall HMAC key v z,
    0 <= z ->
    (forall x y, Zlength (HMAC x y) = 32) ->
    (exists n, z = n * 32) ->
    Zlength (snd (HMAC_DRBG_generate_helper_Z HMAC key v z)) = z.
Proof.
  intros HMAC key v z Hz Hlength Hn.
  destruct Hn as [n Hn].
  rewrite <- (Z2Nat.id n) in Hn by omega.
  generalize dependent z. revert Hlength.
  induction (Z.to_nat n); intros.
  {
    change (Z.of_nat 0) with 0 in Hn.
    change (0 * 32) with 0 in Hn.
    subst.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    reflexivity.
  }
  {
    assert (Hn': z = Z.of_nat n0 * 32 + 32).
    {
      rewrite Nat2Z.inj_succ in Hn.
      rewrite <- Zmult_succ_l_reverse in Hn.
      auto.
    }
    clear Hn.
    rename Hn' into Hn.
    subst z.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    assert (Hf: 0 >=? Z.of_nat n0 * 32 + 32 = false).
    {
      rewrite Z.geb_leb.
      apply Z.leb_gt; omega.
    }
    rewrite Hf.
    remember (HMAC_DRBG_generate_helper_Z HMAC key v
               (Z.of_nat n0 * 32 + 32 - Z.of_nat 32)) as result; destruct result.
    simpl.
    rewrite Zlength_correct.
    rewrite app_length.
    rewrite Nat2Z.inj_add.
    do 2 rewrite <- Zlength_correct.
    rewrite Hlength.
    replace l0 with (snd (HMAC_DRBG_generate_helper_Z HMAC key v
                (Z.of_nat n0 * 32 + 32 - Z.of_nat 32))) by (rewrite <- Heqresult; auto).
    change (Z.of_nat 32) with 32.
    rewrite IHn0; auto; omega.
  }
Qed.

Lemma HMAC_DRBG_generate_helper_Z_incremental_equiv:
  forall HMAC key v z incr,
    0 <= z ->
    0 < incr <= 32 ->
    (exists n, z = n * 32) ->
    HMAC_DRBG_generate_helper_Z HMAC key v (z + incr) = HMAC_DRBG_generate_helper_Z HMAC key v (z + 32).
Proof.
  intros HMAC key v z incr Hz Hlength Hn.
  destruct Hn as [n Hn].
  rewrite <- (Z2Nat.id n) in Hn by omega.
  generalize dependent z.
  induction (Z.to_nat n); intros.
  {
    (* base case *)
    change ((Z.of_nat 0) * 32) with 0 in Hn.
    subst z; simpl.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    assert (Hf: 0 >=? incr = false).
    {
      rewrite Z.geb_leb.
      apply Z.leb_gt; omega.
    }
    rewrite Hf.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    assert (Hf2: 0 >=? incr - Z.of_nat 32 = true).
    {
      change (Z.of_nat 32) with 32.
      rewrite Z.geb_leb.
      apply Z.leb_le; omega.
    }
    rewrite Hf2.
    reflexivity.
  }
  {
    (* inductive case *)
    assert (Hn': z = Z.of_nat n0 * 32 + 32).
    {
      rewrite Nat2Z.inj_succ in Hn.
      rewrite <- Zmult_succ_l_reverse in Hn.
      auto.
    }
    clear Hn; rename Hn' into Hn.
    subst z.
    rewrite HMAC_DRBG_generate_helper_Z_equation.
    assert (Hf: 0 >=? Z.of_nat n0 * 32 + 32 + incr = false).
    {
      rewrite Z.geb_leb.
      apply Z.leb_gt; omega.
    }
    rewrite Hf.
    change (Z.of_nat 32) with 32.
    replace (Z.of_nat n0 * 32 + 32 + incr - 32) with (Z.of_nat n0 * 32 + incr) by omega.
    rewrite IHn0; try omega.
    remember (let (v0, rest) :=
        HMAC_DRBG_generate_helper_Z HMAC key v (Z.of_nat n0 * 32 + 32) in
    (HMAC v0 key, rest ++ HMAC v0 key)) as saved; rewrite HMAC_DRBG_generate_helper_Z_equation; subst saved.
    assert (Hf2: 0 >=? Z.of_nat n0 * 32 + 32 + 32 = false).
    {
      rewrite Z.geb_leb.
      apply Z.leb_gt; omega.
    }
    rewrite Hf2.
    change (Z.of_nat 32) with 32.
    replace (Z.of_nat n0 * 32 + 32 + 32 - 32) with (Z.of_nat n0 * 32 + 32) by omega.
    reflexivity.
  }
Qed.
