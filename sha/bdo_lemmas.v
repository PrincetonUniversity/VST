Require Import floyd.proofauto.
Require Import sha.SHA256.
Require Import sha.sha.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Lemma force_lengthn_firstn:
  forall {A} n b (v:A), (n <= length b)%nat -> 
         force_lengthn n b v = firstn n b.
Proof.
induction n; intros; simpl.
reflexivity.
destruct b. inv H.
simpl in H. f_equal. apply IHn. omega.
Qed.

Lemma Zland_15:
 forall i, Z.land i 15 = i mod 16.
Proof.
intros.
change 15%Z with (Z.ones 4).
rewrite Z.land_ones by (compute; congruence).
reflexivity.
Qed.

Lemma Znth_nthi:
  forall i b,
  (0 <= i < Zlength b)%Z -> Znth i (map Vint b) Vundef = Vint (nthi b i).
Proof.
intros; unfold Znth.
rewrite if_false by omega.
rewrite (@nth_map' int val _ _ Int.zero).
reflexivity.
rewrite Zlength_correct in H.
apply Nat2Z.inj_lt. rewrite Z2Nat.id by omega. omega.
Qed.

Lemma Znth_nthi':
 forall i b,
  Zlength b = 16%Z ->
  Znth (Z.land i 15) (map Vint b) Vundef = Vint (nthi b (i mod 16)).
Proof.
 intros.
 rewrite Zland_15.
 apply Znth_nthi.
 rewrite H.
 apply Z.mod_pos_bound.
 computable.
Qed.

Lemma Zland_in_range:
  forall i, (0 <= Z.land i 15 < 16)%Z.
Proof.
intros.
rewrite Zland_15. apply Z_mod_lt. compute; congruence.
Qed.
Hint Resolve Zland_in_range.


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

Lemma Znth_land_is_int:
  forall i b j, 
  is_int I32 Unsigned (Znth (Z.land i 15) (map Vint (Xarray b j 0)) Vundef).
Proof.
intros.
rewrite Zland_15.
rewrite Znth_nthi.
apply I.
apply Z.mod_pos_bound.
change (Zlength (Xarray b j 0)) with (16%Z).
compute; auto.
Qed.

Hint Resolve Znth_land_is_int.
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
pose proof (skipn_length b (16 - S n)).
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

Lemma length_Xarray:
  forall b i, length (Xarray b i 0) = 16%nat.
Proof.
intros. rewrite Xarray_eq by computable. reflexivity.
Qed.

Lemma Xarray_0: forall b,
    length b = 16%nat -> Xarray b 16 0 = b.
Proof.
intros.
rewrite Xarray_eq. simpl.
do 16 (destruct b; [discriminate | ]).
destruct b; [ | discriminate].
simpl.
repeat (rewrite W_equation; rewrite if_true by (compute; congruence)).
reflexivity.
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

Global Opaque Xarray.

Lemma Xarray_update:
 forall i b,
  length b = LBLOCK ->
  (16 <= i < 64)%nat ->
 upd_reptype_array tuint (Z.of_nat i mod 16)
          (map Vint (Xarray b (Z.of_nat i) 0))
          (Vint (W (nthi b) (Z.of_nat i)))
  = map Vint (Xarray b (Z.of_nat (i+1)) 0).
Proof.
intros.
unfold upd_reptype_array.
assert (0 <= Z.of_nat i mod 16 < 16)%Z
         by (apply Z_mod_lt; compute; congruence).
rewrite force_lengthn_firstn
  by (change (length (map Vint (Xarray b (Z.of_nat i) 0))) with 
        (nat_of_Z 16);
        apply Z2Nat.inj_le; omega).
rewrite firstn_map. 
rewrite skipn_map.
rewrite <- map_cons.
rewrite <- map_app.
f_equal.
change nat_of_Z with Z.to_nat.
rewrite Z2Nat.inj_add by omega.
change (Z.to_nat 1) with 1%nat.
repeat rewrite Xarray_eq by omega.
repeat match type of H0 with
| (64 <= _ < _)%nat => elimtype False; omega
| (?A <= _ < _)%nat =>
 assert (H9: i=A \/ (A+1 <= i < 64)%nat) by omega;
 clear H0; destruct H9 as [H0|H0];
 [subst i; reflexivity
 | simpl in H0 ]
end.
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

