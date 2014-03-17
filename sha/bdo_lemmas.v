Require Import proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.sha_lemmas2.

Definition Xarray (b: list int) (i j: Z) :=
   tuints (rev (generate_word (rev b) 48)) (i-16+(j-i) mod 16).

Lemma array_at_Xarray:
 forall b, 
    length b = 16%nat ->
    array_at tuint Tsh (Xarray b 16) 0 16 = array_at tuint Tsh (tuints b) 0 16.
Proof.
intros.
apply array_at_ext; intros j ?.
unfold Xarray, tuints, ZnthV.
change (16-16)%Z with 0%Z.
rewrite Z.add_0_l.
assert (0 <= (j-16)mod 16 < 16)%Z by (apply Z.mod_pos_bound; omega).
rewrite if_false by omega.
rewrite if_false by omega.
rewrite Zminus_mod. rewrite Z.mod_same by omega.
rewrite Z.sub_0_r. rewrite Z.mod_mod by omega.
rewrite Z.mod_small by auto.
assert (Z.to_nat j < length b)%nat 
 by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by omega; rewrite H; apply H0).
rewrite (@nth_map' int val _ _ Int.zero).
rewrite (@nth_map' int val _ _ Int.zero) by auto.
f_equal.
rewrite (generate_word_small (Z.to_nat j)); auto.
rewrite rev_length, length_generate_word, rev_length; omega.
Qed.

Lemma X_subscript_aux:
  forall n (b: list int) (i: nat), 
  (16 <= Z.of_nat i < 64)%Z ->
  length b = LBLOCK ->
  is_int
  (Xarray b (Z.of_nat i)
    (Int.signed (Int.and (Int.repr (Z.of_nat i + n)) (Int.repr 15)))).
Proof.
intros.
unfold Xarray, tuints,ZnthV.
 pose proof  (and_mod_15_lem (Z.of_nat i + n)).
 forget (Int.signed (Int.and (Int.repr (Z.of_nat i + n)) (Int.repr 15))) as k.
 assert (0 <= (k - Z.of_nat i) mod 16 < 16)%Z
  by ( apply  Z.mod_pos_bound; omega).
 rewrite if_false by omega.
 rewrite (@nth_map' int val _ _ Int.zero). apply I.
 rewrite rev_length, length_generate_word, rev_length, H0.
 change (LBLOCK+48)%nat with 64%nat.
 change 64%nat with (Z.to_nat 64).
 apply Z2Nat.inj_lt; omega.
Qed.


Lemma extract_from_b:
  forall b i n,
    length b = 16%nat ->
    (16 <= i < 64)%nat ->
    (0 <= n < 16)%Z ->
    (Xarray b (Z.of_nat i) ((Z.of_nat i + n) mod 16) = Vint (nthB b i n))%Z.
Proof.
intros.
assert (0 <= (Z.of_nat i + n) mod 16 < 16)%Z by (apply Z_mod_lt; clear; omega).
unfold Xarray, tuints, ZnthV.
replace (((Z.of_nat i + n) mod 16 - Z.of_nat i) mod 16)%Z 
  with (n mod 16)%Z
 by (rewrite Zminus_mod, Zmod_mod, <- Zminus_mod; f_equal; omega).
 rewrite Z.mod_small by omega.
rewrite if_false by omega.
rewrite (@nth_map' int val _ _ Int.zero)
 by (rewrite rev_length, length_generate_word, rev_length, H;
      change (16+48)%nat with (Z.to_nat 64);
      apply Z2Nat.inj_lt; omega).
unfold nthB.
reflexivity.
Qed.

Lemma X_subscript_aux2:
  forall n, 0 <= n < Int.max_unsigned -> 
        Int.signed (Int.and (Int.repr n) (Int.repr 15)) = n mod 16.
Proof.
intros. unfold Int.and. rewrite (Int.unsigned_repr 15) by repable_signed.
 change 15 with (Z.ones 4). rewrite Z.land_ones by repable_signed.
 rewrite Int.unsigned_repr by repable_signed.
 rewrite Int.signed_repr. f_equal.
 destruct H.
 pose proof (Z.mod_bound_pos n 16 H).
 change (2^4) with 16. repable_signed. 
Qed.


Definition c64 := 64%nat.  Global Opaque c64.
Definition c48 := 48%nat.  Global Opaque c48.

Lemma Xarray_update:
 forall i bb,
  length bb = LBLOCK ->
  (16 <= i < 64)%nat ->
   array_at tuint Tsh 
   (upd (Xarray bb (Z.of_nat i)) (Z.of_nat i mod 16)
          (Vint
             (Int.add (nthB bb i 0)
                (Int.add
                   (Int.add (sigma_0 (nthB bb i 1)) (sigma_1 (nthB bb i 14)))
                   (nthB bb i 9))))) 0 LBLOCKz =
  array_at tuint Tsh (Xarray bb (Z.of_nat (i + 1))) 0 LBLOCKz.
Proof.
intros.
change LBLOCKz with 16. change LBLOCK with 16%nat.
apply array_at_ext; intros j ?.
unfold upd, Xarray, tuints, ZnthV.

assert ((Z.of_nat (i + 1) - 16 + (Z.of_nat i mod 16 - Z.of_nat (i + 1)) mod 16)
            = Z.of_nat i). {
rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1%Z.
rewrite Zminus_mod. rewrite Z.mod_mod by computable.
rewrite <- Zminus_mod.
replace (Z.of_nat i - (Z.of_nat i + 1)) with (-1)%Z by omega.
change (-1 mod 16) with 15%Z.
replace (Z.of_nat i + 1 - 16 + 15) with (Z.of_nat i) by omega.
auto.
}
if_tac.
subst j.
rewrite H2.
rewrite if_false by omega.
rewrite (@nth_map' int val _ _ Int.zero)
 by (rewrite rev_length, length_generate_word, rev_length, H, Nat2Z.id; apply H0).
f_equal.
rewrite nth_rev_generate_word; try rewrite Nat2Z.id; auto.
rewrite if_false.
rewrite if_false.
f_equal. f_equal.
rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
replace ((j - Z.of_nat i) mod 16) with ((j - (Z.of_nat i + 1)) mod 16 + 1); [omega|].
replace (j - (Z.of_nat i + 1)) with (j-Z.of_nat i - 1) by (clear; omega).
rewrite Zminus_mod.
rewrite (Zminus_mod j).
rewrite (Z.mod_small _ _ H1).
clear - H1 H3.
assert (0 <= Z.of_nat i mod 16 < 16) by (apply Z.mod_pos_bound; omega).
forget (Z.of_nat i mod 16) as k.
clear i.
assert ((j-k) mod 16 <> 0).
intro.
assert (-16 < j-k < 16) by omega.
destruct (zlt (j-k) 0).
apply Z.mod_opp_l_z in H0; try computable.
replace (-(j-k)) with (k-j) in H0 by omega.
rewrite Z.mod_small in H0 by omega. omega.
rewrite Z.mod_small in H0 by omega. omega.
forget (j-k) as n.
clear - H0.
rewrite Z.mod_small.
change (1 mod 16) with 1; omega.
change (1 mod 16) with 1.
assert (0 <= n mod 16 < 16)  by (apply Z.mod_pos_bound; omega).
omega.
apply Zle_not_lt.
clear - H0.
assert (0 <= (j - Z.of_nat (i + 1)) mod 16 < 16)  by (apply Z.mod_pos_bound; omega).
forget ((j - Z.of_nat (i + 1)) mod 16) as m.
destruct H0 as [H0 _].
apply Nat2Z.inj_le in H0. change (Z.of_nat 16) with 16 in H0.
rewrite Nat2Z.inj_add. change (Z.of_nat 1) with 1.
omega.
apply Zle_not_lt.
clear - H0.
assert (0 <= (j - Z.of_nat i) mod 16 < 16)  by (apply Z.mod_pos_bound; omega).
forget ((j - Z.of_nat i) mod 16) as m.
destruct H0 as [H0 _].
apply Nat2Z.inj_le in H0. change (Z.of_nat 16) with 16 in H0.
omega.
Qed.

