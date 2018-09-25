Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import VST.floyd.functional_base.
Require Import sha.HMAC256_functional_prog.

Definition HKDF_extract (salt IKM: list byte): list byte := HMAC256 IKM salt.

Function Ti (PRK info: list byte) n:=
  match n with
  O => nil 
 |S m => let prev := Ti PRK info m in
         HMAC256 (prev ++ info ++ [Byte.repr (Z.of_nat n)]) PRK
  end.

Function T (PRK info: list byte) (n:nat):list byte :=
  match n with
  O => nil
| S m => (T PRK info m) ++ (Ti PRK info n)
  end.

Definition HKDF_expand (PRK info:list byte) (L:Z):list byte :=
  if zle L 0 then nil else
  let N := Z.of_nat SHA256.DigestLength in 
  let k := if zeq (L mod N) 0 then Z.div L N else (Z.div L N) + 1 in
  floyd.sublist.sublist 0 L (T PRK info (Z.to_nat k)).

Definition HKDF salt IKM info L:=
  let PRK := HKDF_extract salt IKM in
  HKDF_expand PRK info L.


(************************************ Test vectors**************************)

Require Import Coq.Strings.String.
Definition decode_hex := sha.functional_prog.hexstring_to_bytelist. 

Module HKDF_test_rfc5869_A1.
Definition IKM   := decode_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b".
Definition salt  := decode_hex "000102030405060708090a0b0c".
Definition info  := decode_hex "f0f1f2f3f4f5f6f7f8f9".
Definition L     := 42.
Definition PRK   := decode_hex "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5".
Definition OKM   := decode_hex "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865".

Goal map Byte.unsigned (HKDF_extract salt IKM) = map Byte.unsigned PRK.
  vm_compute; reflexivity. Qed. 
Goal map Byte.unsigned (HKDF salt IKM info L) = map Byte.unsigned OKM.
    vm_compute. reflexivity. Qed. (*6secs*)
End HKDF_test_rfc5869_A1.

Module HKDF_test_rfc5869_A2.
Definition IKM   := decode_hex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f".
Definition salt  := decode_hex "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeaf".
Definition info  := decode_hex "b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff".
Definition L     := 82.

Definition PRK   := decode_hex "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244".
Definition OKM   := decode_hex "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87".

Goal map Byte.unsigned (HKDF_extract salt IKM) = map Byte.unsigned PRK.
     vm_compute.  reflexivity. Qed. 
Goal map Byte.unsigned (HKDF salt IKM info L) = map Byte.unsigned OKM.
     vm_compute. reflexivity. Qed.
End HKDF_test_rfc5869_A2.

Module HKDF_test_rfc5869_A3.
Definition IKM   := decode_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b".
Definition salt  := decode_hex "".
Definition info  := decode_hex "".
Definition L     := 42.

Definition PRK   := decode_hex "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04".
Definition OKM   := decode_hex "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8".

Goal map Byte.unsigned (HKDF_extract salt IKM) = map Byte.unsigned PRK.
   vm_compute.  reflexivity. Qed. 
Goal map Byte.unsigned (HKDF salt IKM info L) = map Byte.unsigned OKM.
   vm_compute. reflexivity. Qed.
End HKDF_test_rfc5869_A3.


(********************************Lemmas*************************************)

Require Import VST.msl.Coqlib2.
Require Import compcert.lib.Integers.
Require Import VST.floyd.sublist.
Require Import sha.hmac_common_lemmas.

Lemma Zlength_Ti PRK INFO n: Zlength (Ti PRK INFO n) = match n with O => 0 | S k => 32 end.
Proof. destruct n; simpl. apply Zlength_nil. apply HMAC_Zlength. Qed.

Lemma Zlength_T PRK INFO n: Zlength (T PRK INFO n) = Z.of_nat (32 *n).
Proof. induction n.
apply Zlength_nil.
replace (T PRK INFO (S n)) with ((T PRK INFO n) ++ (Ti PRK INFO (S n))) by reflexivity.
rewrite Zlength_app, IHn, Zlength_Ti.
do 2 rewrite Nat2Z.inj_mul. rewrite (Nat2Z.inj_succ n), Zmult_succ_r_reverse; trivial.
Qed.

Lemma Zlength_HKDF_expand x y z rest: 0 <= 32 * z -> 0 <= rest < 32 -> 
      (Zlength (HKDF_expand x y (32*z+rest)) = 32*z+rest)%Z.
Proof. unfold HKDF_expand; intros.
destruct (zle (32*z+rest) 0).
+ rewrite Zlength_nil; omega.
+ rewrite Zlength_sublist; try omega. simpl.
  rewrite Zlength_T.
  destruct (zeq rest 0).
  - subst rest. rewrite Z.add_0_r in *.
    assert (X: (32 * z) mod 32 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
    rewrite X, if_true; trivial. 
    assert (Y: (32 * z) / 32 = z). rewrite Z.mul_comm; apply Z_div_mult_full; omega.
    rewrite Y, Nat2Z.inj_mul, Z2Nat.id; simpl; omega. 
  - rewrite if_false. 
    * replace (32 * z + rest) with (z * 32 + rest) by omega.
      rewrite Z_div_plus_full_l, Zdiv_small, Zplus_0_r; try omega.
      rewrite Nat2Z.inj_mul, Z2Nat.id. simpl. 2: omega.
      rewrite Z.mul_add_distr_l, Z.mul_1_r. omega.
    * intros N. replace (32 * z + rest) with (rest + z * 32) in N by omega.
      rewrite Z_mod_plus, Zmod_small in N; omega.
Qed.

Lemma sublist_HKDF_expand1 prk info i r (I: 0 <= i) (R:0<=r<32): 
    sublist 0 (32 * i) (HKDF_expand prk info (32*i)) =
    sublist 0 (32 * i) (HKDF_expand prk info (32*i+r)).
Proof. unfold HKDF_expand.
destruct (zle (32 * i) 0); simpl.
+ assert (i=0) by omega. subst i. simpl. rewrite Z.add_0_l.
  destruct (zle r 0); trivial.
+ destruct (zle (32 * i + r) 0); try omega. 
    rewrite (Zmod_unique _ _ i 0); try omega. simpl. 
    rewrite (Zdiv_unique _ _ i 0); try omega.
    rewrite (Zmod_unique _ _ i r); try omega. 
    rewrite (Zdiv_unique _ _ i r); try omega.
  rewrite 2 sublist_sublist; try omega. simpl. rewrite Z.add_0_r.
  destruct (zeq r 0); simpl; trivial.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    2: rewrite Z.add_comm, Z2Nat.inj_add; try reflexivity; try omega.
  simpl. rewrite sublist_app1; trivial. omega.
      rewrite Zlength_T, Nat2Z.inj_mul, Z2Nat.id; simpl; omega.
Qed.

Lemma sublist_HKDF_expand2 prk info i (I: 0 <= i) : 
    sublist 0 (32 * i) (HKDF_expand prk info (32*i)) =
    sublist 0 (32 * i) (HKDF_expand prk info (32*(i+1))).
Proof. unfold HKDF_expand.
destruct (zle (32 * i) 0); simpl.
+ assert (i=0) by omega. subst i; simpl. reflexivity.
+ destruct (zle (32 * (i + 1)) 0); try omega. 
    rewrite (Zmod_unique _ _ i 0); try omega. simpl. 
    rewrite (Zdiv_unique _ _ i 0); try omega.
    rewrite (Zmod_unique _ _ (i+1) 0); try omega. 
    rewrite (Zdiv_unique _ _ (i+1) 0); try omega. simpl.
  rewrite 2 sublist_sublist; try omega. simpl. rewrite Z.add_0_r.
  replace (Z.to_nat (i+1)) with (S (Z.to_nat i)).
    2: rewrite Z.add_comm, Z2Nat.inj_add; try reflexivity; try omega.
  simpl. rewrite sublist_app1; trivial. omega.
  rewrite Zlength_T, Nat2Z.inj_mul, Z2Nat.id; simpl; omega.
Qed.

Lemma sublist_HKDF_expand3 prk info i rest (REST : 0 < rest < 32)
      (OLEN : 0 <= 32 * i + rest):
  sublist 0 (32 * i + rest) (HKDF_expand prk info (32 * i + 32)) =
  HKDF_expand prk info (32 * i + rest).
Proof.
            unfold HKDF_expand. simpl. destruct (zle (32 * i + 32) 0); try omega.
            destruct (zle (32 * i + rest) 0); try omega.
            rewrite sublist_sublist; try omega. rewrite 2 Z.add_0_r.
            erewrite (Zmod_unique _ _(i+1) 0); try omega. simpl. 
            erewrite (Zdiv_unique _ _(i+1) 0); try omega.
            erewrite (Zmod_unique _ _ i rest); try omega. rewrite if_false; try omega.
            erewrite (Zdiv_unique _ _ i rest); try omega; trivial.
Qed.
