Require Import proofauto.
Require Import sha.SHA256.
Require Import sha.sha.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Lemma and_mone':
 forall x, Int.and x (Int.repr (-1)) = x.
Proof.
apply Int.and_mone.
Qed.

Lemma Sigma_1_eq: forall f_,
  Sigma_1 f_ =
            (Int.xor
              (Int.xor
                 (Int.or (Int.shl f_ (Int.repr 26))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 26))))
                 (Int.or (Int.shl f_ (Int.repr 21))
                    (Int.shru (Int.and f_ (Int.repr (-1)))
                       (Int.sub (Int.repr 32) (Int.repr 21)))))
              (Int.or (Int.shl f_ (Int.repr 7))
                 (Int.shru (Int.and f_ (Int.repr (-1)))
                    (Int.sub (Int.repr 32) (Int.repr 7))))).
Proof.
intros.
unfold Sigma_1, Rotr.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 26)) with (Int.repr 6).
change (Int.sub (Int.repr 32) (Int.repr 21)) with (Int.repr 11).
change (Int.sub (Int.repr 32) (Int.repr 7)) with (Int.repr 25).
reflexivity.
Qed.

Lemma  Sigma_0_eq: forall b_,
   Sigma_0 b_ = 
      (Int.xor
        (Int.xor
           (Int.or (Int.shl b_ (Int.repr 30))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 30))))
           (Int.or (Int.shl b_ (Int.repr 19))
              (Int.shru (Int.and b_ (Int.repr (-1)))
                 (Int.sub (Int.repr 32) (Int.repr 19)))))
        (Int.or (Int.shl b_ (Int.repr 10))
           (Int.shru (Int.and b_ (Int.repr (-1)))
              (Int.sub (Int.repr 32) (Int.repr 10))))).
Proof.
intros.
unfold Sigma_0, Rotr.
repeat rewrite and_mone'.
repeat rewrite <- Int.or_ror by reflexivity.
change (Int.sub (Int.repr 32) (Int.repr 19)) with (Int.repr 13).
change (Int.sub (Int.repr 32) (Int.repr 10)) with (Int.repr 22).
change (Int.sub (Int.repr 32) (Int.repr 30)) with (Int.repr 2).
reflexivity.
Qed.

Lemma Ch_eq: forall f_ g_ h_,
  Ch f_ g_ h_ =
        (Int.xor (Int.and f_ g_) (Int.and (Int.not f_) h_)).
Proof. reflexivity.
Qed.

Lemma Maj_eq:
  forall b c d, 
  Maj b c d =
  (Int.xor (Int.xor (Int.and b c) (Int.and b d)) (Int.and c d)).
Proof.
intros.
unfold Maj.
rewrite (Int.xor_commut) at 1.
rewrite Int.xor_assoc. auto.
Qed.

Lemma sigma_1_eq:
 forall s, sigma_1 s = 
   Int.xor
     (Int.xor
        (Int.or (Int.shl s (Int.repr 15))
           (Int.shru s (Int.sub (Int.repr 32) (Int.repr 15))))
        (Int.or (Int.shl s (Int.repr 13))
           (Int.shru s (Int.sub (Int.repr 32) (Int.repr 13)))))
  (Int.shru s (Int.repr 10)).
Proof.
intros.
unfold sigma_1.
f_equal. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
Qed.

Lemma sigma_0_eq:
 forall s, sigma_0 s = 
  Int.xor
   (Int.xor
     (Int.or (Int.shl s (Int.repr 25))
        (Int.shru s (Int.sub (Int.repr 32) (Int.repr 25))))
     (Int.or (Int.shl s (Int.repr 14))
        (Int.shru s (Int.sub (Int.repr 32) (Int.repr 14)))))
   (Int.shru s (Int.repr 3)).
Proof.
intros.
unfold sigma_0.
f_equal. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
repeat rewrite <- Int.or_ror by reflexivity.
unfold Rotr. f_equal.
Qed.

Lemma and_mod_15_lem:
 forall (n: Z), 
 (0 <= Int.signed (Int.and (Int.repr n) (Int.repr 15)) < 16)%Z.
Proof.
intro n.
unfold Int.and.
rewrite (Int.unsigned_repr 15) by repable_signed.
change 15%Z with (Z.ones 4).
assert (0 <= Z.land (Int.unsigned (Int.repr n)) (Z.ones 4) < 16)%Z.
rewrite Z.land_ones.
apply Z.mod_bound_pos. 
apply Int.unsigned_range. clear; omega. clear; omega.
rewrite Int.signed_repr; auto.
repable_signed.
Qed.

Definition rearrange_regs :=
(Ssequence
     (Sset _T1
        (Ebinop Oadd
           (Ebinop Oadd
              (Ebinop Oadd
                 (Ebinop Oadd (Etempvar _l tuint) (Etempvar _h tuint) tuint)
                 (Ebinop Oxor
                    (Ebinop Oxor
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _e tuint)
                             (Econst_int (Int.repr 26) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _e tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 26) tint) tint) tuint)
                          tuint)
                       (Ebinop Oor
                          (Ebinop Oshl (Etempvar _e tuint)
                             (Econst_int (Int.repr 21) tint) tuint)
                          (Ebinop Oshr
                             (Ebinop Oand (Etempvar _e tuint)
                                (Econst_int (Int.repr (-1)) tuint) tuint)
                             (Ebinop Osub (Econst_int (Int.repr 32) tint)
                                (Econst_int (Int.repr 21) tint) tint) tuint)
                          tuint) tuint)
                    (Ebinop Oor
                       (Ebinop Oshl (Etempvar _e tuint)
                          (Econst_int (Int.repr 7) tint) tuint)
                       (Ebinop Oshr
                          (Ebinop Oand (Etempvar _e tuint)
                             (Econst_int (Int.repr (-1)) tuint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 7) tint) tint) tuint)
                       tuint) tuint) tuint)
              (Ebinop Oxor
                 (Ebinop Oand (Etempvar _e tuint) (Etempvar _f tuint) tuint)
                 (Ebinop Oand (Eunop Onotint (Etempvar _e tuint) tuint)
                    (Etempvar _g tuint) tuint) tuint) tuint)
           (Etempvar _Ki tuint) tuint))
     (Ssequence
        (Sset _T2
           (Ebinop Oadd
              (Ebinop Oxor
                 (Ebinop Oxor
                    (Ebinop Oor
                       (Ebinop Oshl (Etempvar _a tuint)
                          (Econst_int (Int.repr 30) tint) tuint)
                       (Ebinop Oshr
                          (Ebinop Oand (Etempvar _a tuint)
                             (Econst_int (Int.repr (-1)) tuint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 30) tint) tint) tuint)
                       tuint)
                    (Ebinop Oor
                       (Ebinop Oshl (Etempvar _a tuint)
                          (Econst_int (Int.repr 19) tint) tuint)
                       (Ebinop Oshr
                          (Ebinop Oand (Etempvar _a tuint)
                             (Econst_int (Int.repr (-1)) tuint) tuint)
                          (Ebinop Osub (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 19) tint) tint) tuint)
                       tuint) tuint)
                 (Ebinop Oor
                    (Ebinop Oshl (Etempvar _a tuint)
                       (Econst_int (Int.repr 10) tint) tuint)
                    (Ebinop Oshr
                       (Ebinop Oand (Etempvar _a tuint)
                          (Econst_int (Int.repr (-1)) tuint) tuint)
                       (Ebinop Osub (Econst_int (Int.repr 32) tint)
                          (Econst_int (Int.repr 10) tint) tint) tuint) tuint)
                 tuint)
              (Ebinop Oxor
                 (Ebinop Oxor
                    (Ebinop Oand (Etempvar _a tuint) (Etempvar _b tuint)
                       tuint)
                    (Ebinop Oand (Etempvar _a tuint) (Etempvar _c tuint)
                       tuint) tuint)
                 (Ebinop Oand (Etempvar _b tuint) (Etempvar _c tuint) tuint)
                 tuint) tuint))
        (Ssequence (Sset _h (Etempvar _g tuint))
           (Ssequence (Sset _g (Etempvar _f tuint))
              (Ssequence (Sset _f (Etempvar _e tuint))
                 (Ssequence
                    (Sset _e
                       (Ebinop Oadd (Etempvar _d tuint) (Etempvar _T1 tuint)
                          tuint))
                    (Ssequence (Sset _d (Etempvar _c tuint))
                       (Ssequence (Sset _c (Etempvar _b tuint))
                          (Ssequence (Sset _b (Etempvar _a tuint))
                             (Sset _a
                                (Ebinop Oadd (Etempvar _T1 tuint)
                                   (Etempvar _T2 tuint) tuint))))))))))).


Definition Delta_loop1 : tycontext.
simplify_Delta_from
 (initialized _i
          (initialized _h
           (initialized _g
              (initialized _f
                 (initialized _e
                    (initialized _d
                       (initialized _c
                          (initialized _b
                             (initialized _a
                                (initialized _data
     (func_tycontext f_sha256_block_data_order Vprog Gtot))))))))))).
Defined.


Function Xarray (b: list int) (i j: Z) {measure (fun j => Z.to_nat (16-j)) j} : list int :=
 if zlt j 16
  then W (nthi b) (i - 16 + (j-i) mod 16) :: Xarray b i (j+1)
  else nil.
Proof.
intros.
apply Z2Nat.inj_lt; omega.
Defined. 

(*Definition Xarray (b: list int) (i j: Z) :=
    Vint (W (nthi b) (i-16+(j-i) mod 16)).
*)

Lemma Xarray_simpl:
   forall b, length b = 16%nat -> Xarray b 16 0 = b.
Proof.
intros.
assert (forall n, (n<=16)%nat -> Xarray b 16 (16- Z.of_nat n) = skipn (16-n) b);
  [ |apply (H0 16%nat); omega ].
induction n; intros.
rewrite Xarray_equation.
simpl Z.of_nat.
rewrite if_false by omega.
rewrite skipn_short; auto; omega.
rewrite inj_S.
rewrite Xarray_equation.
rewrite if_true by omega.
replace (16 - Z.succ (Z.of_nat n)+1) with (16 - Z.of_nat n) by omega.
rewrite IHn by omega.
clear IHn.
replace (16 - n)%nat with (S (16 - S n))%nat by omega.
rewrite <- inj_S.
replace (16 - Z.of_nat (S n)) with (Z.of_nat (16 - S n))
  by (rewrite Nat2Z.inj_sub by omega; reflexivity).
replace (S (16 - S n)) with ( (16 - S n)+ 1)%nat by omega.
rewrite <- skipn_skipn.
etransitivity.
Focus 2.
apply (firstn_skipn 1).
assert (H1: firstn 1 (skipn (16 - S n) b) = 
            W (nthi b) (16 - 16 + (Z.of_nat (16 - S n) - 16) mod 16) :: nil);
  [ | rewrite H1; reflexivity].
unfold firstn.
destruct (skipn (16 - S n) b) eqn:?.
pose proof (skipn_length (16 - S n) b).
spec H1; [omega | ].
rewrite Heql in H1.
simpl length in H1.
omega.
f_equal.
pose proof (nth_skipn _ 0 (16 - S n) b Int.zero).
rewrite Heql in H1.
unfold nth at 1 in H1.
subst.
rewrite Z.sub_diag. rewrite Z.add_0_l.
rewrite plus_0_l.
rewrite Zminus_mod.
rewrite Z.mod_same by omega. rewrite Z.sub_0_r. 
rewrite Z.mod_mod by omega.
assert (0 <= (Z.of_nat (16 - S n))mod 16 < 16)%Z by (apply Z.mod_pos_bound; omega).
rewrite W_equation.
rewrite if_true by  omega.
rewrite Z.mod_small.
unfold nthi.
rewrite Nat2Z.id.
reflexivity.
split; try omega.
change (Z.of_nat (16 - S n) < Z.of_nat 16).
apply Nat2Z.inj_lt.
omega.
Qed.

(*
Lemma array_at_Xarray:
 forall b, 
    length b = 16%nat ->
    array_at Tsh (tarray tuint 16) nil 0 16 (Xarray b 16 0) = array_at Tsh (tarray tuint 16) nil 0 16 (map Vint b).
Proof.
intros.
apply array_at_ext; intros j ?.
unfold Xarray, tuints, ZnthV.
change (16-16)%Z with 0%Z.
rewrite Z.add_0_l.
assert (0 <= (j-16)mod 16 < 16)%Z by (apply Z.mod_pos_bound; omega).
rewrite if_false by omega.
assert (Z.to_nat j < length b)%nat 
 by (apply Nat2Z.inj_lt; rewrite Z2Nat.id by omega; rewrite H; apply H0).
rewrite (@nth_map' int val _ _ Int.zero); auto.
f_equal.
rewrite W_equation.
rewrite if_true by omega.
unfold nthi.
f_equal.
f_equal.
rewrite Zminus_mod.
rewrite Z.mod_same by omega. rewrite Z.sub_0_r. 
rewrite Z.mod_mod by omega.
apply Z.mod_small; omega.
Qed. 
*)

(*
Lemma is_int_Xarray:
 forall b i j, is_int I32 Unsigned (Xarray b i j).
Proof.
intros. apply I.
Qed.
*)


Fixpoint Xarray' (b: list int) (i: Z) (k: nat) : list int :=
 match k with
 | O => nil
 | S k' => W (nthi b) (i - 16 + (16-(Z.of_nat k)-i) mod 16) :: 
                 Xarray' b i k'
 end.
Lemma Xarray_eq:
    forall b i j, 0 <= j < 16 -> Xarray b i j = Xarray' b i (Z.to_nat (16-j)).
Proof.
intros.
remember (Z.to_nat (16-j)) as k.
replace j with (16- Z.of_nat k)
 by (subst k; rewrite Z2Nat.id; omega).
assert (k<=16)%nat.
subst.
change (Z.to_nat (16 - j) <= Z.to_nat 16)%nat.
apply Z2Nat.inj_le; try omega.
clear - H0.
revert H0; induction k; intros.
change (Z.of_nat 0) with 0. rewrite Z.sub_0_r.
rewrite Xarray_equation.
rewrite if_false by omega.
reflexivity.
simpl Xarray'.
rewrite Xarray_equation.
rewrite if_true by (rewrite inj_S; omega).
f_equal.
rewrite <- IHk by omega.
f_equal.
rewrite inj_S.
omega.
Qed.

Lemma nth_Xarray':
  forall b i k,
     0 <= k < 16 ->
  nthi (Xarray' b i 16) k =
     W (nthi b) (i - 16 + (k-i) mod 16) .
Proof.
intros.
unfold nthi at 1.
remember (Z.to_nat k) as k'.
rewrite <- (Nat2Z.id k') in Heqk'.
apply Z2Nat.inj in Heqk'; try omega.
subst k.
assert (k'<16)%nat by omega.
clear H.
do 16 (destruct k'; try reflexivity).
omega.
Qed.

Lemma extract_from_b:
  forall b i n,
    length b = 16%nat ->
    16 <= i < 64 ->
    (0 <= n < 16)%Z ->
    nthi (Xarray b i 0) ((i + n) mod 16) = W (nthi b) (i - 16 + n).
Proof.
intros.
rewrite Xarray_eq by omega.
rewrite nth_Xarray' by (apply Z.mod_pos_bound; omega).
f_equal.
f_equal.
rewrite Zminus_mod.
rewrite Zmod_mod.
rewrite Zplus_mod.
rewrite <- Zminus_mod.
rewrite (Zmod_small n) by omega.
replace (i mod 16 + n - i) with (i mod 16 - i + n) by omega.
rewrite Zplus_mod.
rewrite Zminus_mod.
rewrite Zmod_mod.
rewrite Z.sub_diag.
rewrite (Zmod_small 0) by omega.
rewrite Z.add_0_l.
repeat rewrite Zmod_mod.
apply Zmod_small; omega.
Qed.

(*
Lemma Xarray_update:
 forall i bb,
  length bb = LBLOCK ->
  (16 <= i < 64)%nat ->
   data_at Tsh (tarray tuint 16)
   (upd (Xarray bb (Z.of_nat i)) (Z.of_nat i mod 16)
          (Vint (W (nthi bb) (Z.of_nat i)))) =
   data_at Tsh  (tarray tuint 16) (Xarray bb (Z.of_nat (i + 1))) .
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
auto.
f_equal.
f_equal.
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
Qed.
*)

Global Opaque Xarray.

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

