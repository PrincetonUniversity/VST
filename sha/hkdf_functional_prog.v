Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import sha.HMAC256_functional_prog.

Definition HKFD_extract (salt IKM: list Z): list Z := HMAC256 IKM salt.

Function Ti (PRK info: list Z) n:=
  match n with
  O => nil 
 |S m => let prev := Ti PRK info m in
         HMAC256 (prev ++ info ++ [Z.of_nat n]) PRK
  end.

Function T (PRK info: list Z) (n:nat):list Z :=
  match n with
  O => nil
| S m => (T PRK info m) ++ (Ti PRK info n)
  end.

Definition HKDF_expand (PRK info:list Z) (L:Z):list Z :=
  if zle L 0 then nil else
  let N := Z.of_nat SHA256.DigestLength in 
  let k := if zeq (L mod N) 0 then Z.div L N else (Z.div L N) + 1 in
  floyd.sublist.sublist 0 L (T PRK info (Z.to_nat k)).

Definition HKDF salt IKM info L:=
  let PRK := HKFD_extract salt IKM in
  HKDF_expand PRK info L.

Require Import Coq.Strings.String.
Definition decode_hex := sha.functional_prog.hexstring_to_Zlist. 

Module HKDF_test_A1.
(*Test case A.1 from https://github.com/casebeer/python-hkdf/blob/master/tests.py#L63*)
Definition IKM   := decode_hex "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b".
Definition salt  := decode_hex "000102030405060708090a0b0c".
Definition info  := decode_hex "f0f1f2f3f4f5f6f7f8f9".
Definition L     := 42.
Definition PRK   := decode_hex "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5".
Definition OKM   := decode_hex "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865".

Goal HKFD_extract salt IKM = PRK. vm_compute.  reflexivity. Qed. 
Goal HKDF salt IKM info L = OKM. Time vm_compute. (*6secs*) reflexivity. Time Qed. (*6secs*)
End HKDF_test_A1.

Module HKDF_test_A2.
(*Test case A.2 from https://github.com/casebeer/python-hkdf/blob/master/tests.py#L80*)
Definition IKM   := decode_hex "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f".
Definition salt  := decode_hex "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeaf".
Definition info  := decode_hex "b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff".
Definition L     := 82.

Definition PRK   := decode_hex "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244".
Definition OKM   := decode_hex "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87".

Goal HKFD_extract salt IKM = PRK. vm_compute.  reflexivity. Qed. 
Goal HKDF salt IKM info L = OKM. Time vm_compute. (*20secs*) reflexivity. Time Qed. (*20secs*)
End HKDF_test_A2.
