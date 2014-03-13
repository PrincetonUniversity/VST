Require Import proofauto.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Lemma generate_word_lemma1:
  forall b n, length b = LBLOCK ->
   firstn LBLOCK (rev (generate_word (rev b) n)) = b.
Proof.
intros.
change (rev b) with (nil ++ rev b).
forget (@nil int) as a.
Transparent generate_word.
revert a; induction n; intro.
unfold generate_word.
rewrite rev_app_distr.
rewrite rev_involutive.
rewrite firstn_app1 by omega.
rewrite firstn_same; auto; omega.
unfold generate_word; fold generate_word.
change (W (a ++ rev b) :: a ++ rev b) with 
      ((W (a ++ rev b) ::a) ++ rev b).
apply IHn.
Opaque generate_word.
Qed.

Lemma length_generate_word: forall b n,
  length (generate_word b n) = (length b + n)%nat.
Proof.
Transparent generate_word.
intros.
revert b; induction n; intros; simpl.
unfold generate_word; fold generate_word.
omega.
unfold generate_word; fold generate_word.
rewrite IHn.
simpl. omega.
Opaque generate_word.
Qed.

Lemma and_mod_15_lem:
 forall (n: Z), 0 <= Int.signed (Int.and (Int.repr n) (Int.repr 15)) < 16.
Proof.
intro n.
unfold Int.and.
rewrite (Int.unsigned_repr 15) by repable_signed.
change 15 with (Z.ones 4).
assert (0 <= Z.land (Int.unsigned (Int.repr n)) (Z.ones 4) < 16).
rewrite Z.land_ones.
apply Z.mod_bound_pos. 
apply Int.unsigned_range. clear; omega. clear; omega.
rewrite Int.signed_repr; auto.
repable_signed.
Qed.

Transparent generate_word.

Lemma nth_generate_word_S:
  forall k i n b', 
   nth (i+k) (generate_word b' (n+k)) = nth i (generate_word b' n).
Proof.
induction k; intros.
repeat rewrite plus_0_r. auto.
replace (n + S k)%nat with (S (n + k))%nat by omega.
unfold generate_word; fold generate_word.
replace (i + S k)%nat with (S i + k)%nat by omega.
rewrite IHk by (simpl; omega).
clear IHk.
revert i b' ; induction n; intros.
unfold generate_word; fold generate_word.
extensionality d; reflexivity.
unfold generate_word; fold generate_word.
apply IHn.
Qed.

Lemma generate_word_small:
  forall i b n,
           length b = 16%nat ->
           (i < length b)%nat -> 
           nth i (rev (generate_word (rev b) n)) = nth i b.
Proof.
intros.
extensionality d.
rewrite <- (nth_firstn_low _ _ LBLOCK).
rewrite (generate_word_lemma1 b n H).
auto.
rewrite rev_length, length_generate_word, rev_length, H.
change LBLOCK with 16%nat. omega.
Qed.
Opaque generate_word.

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

Definition nthB (b: list int) (i: nat) (n: Z) :=
  nth (Z.to_nat (Z.of_nat i - 16 + n)) (rev (generate_word (rev b) 48)) Int.zero.


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


Transparent generate_word.
Lemma generate_word_plus:
  forall msg a b, (16 <= length msg)%nat ->
         generate_word msg (a+b) = generate_word (generate_word msg a) b.
Proof.
intros msg a b.
revert msg b; induction a; simpl; intros.
unfold generate_word; fold generate_word.
auto.
unfold generate_word; fold generate_word.
rewrite IHa by (simpl; omega).
auto.
Qed.

Lemma nth_rev_generate_word:
 forall i b,
   length b = LBLOCK -> 
   (LBLOCK <= i < 64)%nat ->
    nth i (rev (generate_word (rev b) 48)) Int.zero =
  Int.add (nthB b i 0)
    (Int.add (Int.add (sigma_0 (nthB b i 1)) (sigma_1 (nthB b i 14)))
       (nthB b i 9)).
Proof.
intros.
unfold nthB.
rewrite <- rev_length in H.
forget (rev b) as b'.
clear b.
change LBLOCK with 16%nat in *.
assert (length (generate_word b' 48) = 64)%nat 
 by (rewrite length_generate_word, H; reflexivity).
rewrite rev_nth by omega.
repeat rewrite rev_nth
 by (rewrite H1; change 64%nat with (Z.to_nat 64); apply Z2Nat.inj_lt; omega).
rewrite H1.
rewrite <- (plus_0_l (64 - S i)).
assert (48 = (i - 16) + 1 + (64 - S i))%nat by (clear - H0; omega).
rewrite H2 at 2.
rewrite nth_generate_word_S.
rewrite generate_word_plus by omega.
unfold generate_word at 1. 
unfold nth at 1.
assert (forall n:nat, (n < 16) ->
    ((64 - S (Z.to_nat (Z.of_nat i - 16 + Z.of_nat n))) =
      (16-n) + (48 - S (Z.to_nat (Z.of_nat i - 16)))))%nat.
clear - H0.
intros.
rewrite Z2Nat.inj_add by omega.
rewrite Nat2Z.id.
rewrite Z2Nat.inj_sub by omega.
rewrite Nat2Z.id.
change (Z.to_nat 16) with 16%nat.
omega.
change 0%Z with (Z.of_nat 0); rewrite H3 by (clear; omega).
change 1%Z with (Z.of_nat 1); rewrite H3 by (clear; omega).
change 14%Z with (Z.of_nat 14); rewrite H3 by (clear; omega).
change 9%Z with (Z.of_nat 9); rewrite H3 by (clear; omega).
clear H3.
assert (48 = S (Z.to_nat (Z.of_nat i - 16)) + (48 - S (Z.to_nat (Z.of_nat i - 16))))%nat.
clear - H0.
rewrite Z2Nat.inj_sub by omega.
rewrite Nat2Z.id.
change (Z.to_nat 16) with 16%nat.
omega.
pattern (generate_word b' 48).
rewrite H3 at 1.
repeat rewrite nth_generate_word_S.
rewrite Z2Nat.inj_sub by omega.
rewrite Nat2Z.id.
change (Z.to_nat 16) with 16%nat.
simpl.
change (nth 16) with (@nth int (15+1)).
change (nth 15) with (@nth int (14+1)).
change (nth 2) with (@nth int (1+1)).
change (nth 7) with (@nth int (6+1)).
replace (S (i-16)) with ((i-16)+1)%nat by omega.
repeat rewrite nth_generate_word_S.
assert (length (generate_word b' (i-16)) >= 16)%nat.
rewrite length_generate_word, H; omega.
clear - H4.
forget (generate_word b' (i-16)) as s.
rename H4 into H.
do 16 (destruct s; [simpl in H; omega | ]).
simpl.
rewrite <- Int.add_assoc.
rewrite Int.add_commut.
f_equal.
rewrite Int.add_commut.
rewrite <- Int.add_assoc.
auto.
Qed.
Opaque generate_word.

Lemma nth_error_nth:
  forall A (d: A) i al, (i < length al)%nat -> nth_error al i = Some (nth i al d).
Proof.
induction i; destruct al; simpl; intros; auto.
inv H.
inv H.
apply IHi; omega.
Qed.

